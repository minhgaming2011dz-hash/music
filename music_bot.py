import asyncio
import os
import random
import shutil
import time
from datetime import timedelta
from collections import defaultdict

import discord
from discord import app_commands
import yt_dlp
import spotipy
from spotipy.oauth2 import SpotifyClientCredentials
from aiohttp import web

# ==================== CONFIG ====================

TOKEN = os.environ.get("DISCORD_TOKEN")

try:
    sp = spotipy.Spotify(
        auth_manager=SpotifyClientCredentials(
            client_id=os.environ["SPOTIFY_ID"],
            client_secret=os.environ["SPOTIFY_SECRET"],
        )
    )
except Exception:
    sp = None

YDL_OPTS = {
    "format": "bestaudio/best",
    "noplaylist": True,
    "quiet": True,
    "no_warnings": True,
}

FFMPEG_OPTS = {
    "before_options": (
        "-reconnect 1 "
        "-reconnect_streamed 1 "
        "-reconnect_delay_max 5"
    ),
    "options": "-vn",
}

# Cookies YouTube (không bắt buộc): trên Render thêm Secret File tên cookies.txt
COOKIES_SRC = os.environ.get("YT_COOKIES_FILE", "/etc/secrets/cookies.txt")
COOKIE_OPTS = {}
if os.path.exists(COOKIES_SRC):
    try:
        # Chép sang /tmp vì yt-dlp cần ghi lại cookies, còn /etc/secrets chỉ đọc được
        shutil.copyfile(COOKIES_SRC, "/tmp/yt_cookies.txt")
        COOKIE_OPTS = {"cookiefile": "/tmp/yt_cookies.txt"}
        print("Đã nạp cookies YouTube.")
    except Exception as exc:
        print("Không nạp được cookies YouTube:", exc)
else:
    print("Chưa có cookies YouTube (YouTube có thể chặn IP của server).")
YDL_OPTS.update(COOKIE_OPTS)

# Bài tự động phát tiếp sẽ bỏ qua video dài hơn mức này (livestream, mix hàng giờ...)
AUTO_MAX_SECONDS = 20 * 60

# Tự xóa tin nhắn của bot đã cũ trong kênh được dùng lệnh (mặc định 30 phút).
BOT_MESSAGE_TTL_SECONDS = 30 * 60
MESSAGE_CLEANUP_INTERVAL_SECONDS = 5 * 60

# Dữ liệu riêng cho từng server
queues = defaultdict(list)                  # Hàng đợi phát lần lượt
volumes = defaultdict(lambda: 1.0)           # 1.0 = 100%
music_lists = defaultdict(list)              # Danh sách nhạc người dùng thêm
autoplay = defaultdict(lambda: True)         # Tự phát tiếp khi hàng đợi trống
history = defaultdict(list)                  # Lịch sử bài đã phát
current_song = {}                            # Query bài đang phát
play_channels = {}                           # Kênh nhắn thông báo phát nhạc
command_channels = {}                        # Kênh gần nhất người dùng gọi lệnh bot
play_positions = defaultdict(float)          # Vị trí phát hiện tại (giây)
play_started_at = {}                         # Mốc monotonic khi bài đang chạy
seeking = set()                              # Đang tua bài, ngăn callback tự nhảy bài
return_pending = set()                       # Tránh lặp thao tác /return
now_data = {}                                # Thông tin bài đang/vừa phát (tên, link, id YouTube...)
now_playing_msg = {}                         # Tin nhắn menu điều khiển đang hiện
recent_ids = defaultdict(list)               # id video YouTube đã phát (để không phát lặp)
titles = {}                                  # query/link -> tên bài (để hiển thị đẹp hơn)
stopping = set()                             # Server đang chạy /stop (chặn tự phát bài mới)
auto_paused = set()                          # Server đang tạm dừng vì kênh thoại trống (tự tiếp tục khi có người về)
waiting_for_listener = set()                 # Hết bài lúc kênh trống: chờ có người vào lại mới phát tiếp

# Dữ liệu riêng cho từng người dùng
favorites = defaultdict(list)                # user_id -> [{"title": ..., "url": ...}]


# ==================== SEARCH MUSIC ====================

def extract(query: str) -> dict:
    """Lấy URL stream và tên bài hát bằng yt-dlp."""
    if query.startswith("http"):
        candidates = [query]
    else:
        candidates = [f"ytsearch1:{query}", f"scsearch1:{query}"]

    last_err = None
    for candidate in candidates:
        try:
            with yt_dlp.YoutubeDL(YDL_OPTS) as ydl:
                info = ydl.extract_info(candidate, download=False)

            if not info:
                continue

            if "entries" in info:
                entries = info.get("entries") or []
                if not entries:
                    continue
                info = entries[0]

            if info and info.get("url"):
                return {
                    "url": info["url"],
                    "title": info.get("title", query),
                    "page": info.get("webpage_url")
                    or (candidate if candidate.startswith("http") else None),
                    "yt_id": info.get("id")
                    if info.get("extractor_key") == "Youtube" else None,
                    "duration": info.get("duration"),
                    "uploader": info.get("uploader") or info.get("channel"),
                    "thumbnail": info.get("thumbnail"),
                }
        except Exception as exc:
            last_err = exc

    if last_err:
        raise last_err
    raise RuntimeError("Không tìm thấy bài hát.")


# ==================== SPOTIFY ====================

def spotify_to_queries(link: str) -> list[str]:
    if sp is None:
        raise RuntimeError("Chưa cấu hình SPOTIFY_ID và SPOTIFY_SECRET.")

    if "/track/" in link:
        track = sp.track(link)
        return [f"{track['artists'][0]['name']} - {track['name']}"]

    if "/album/" in link:
        items = sp.album_tracks(link, limit=50)["items"]
        return [
            f"{item['artists'][0]['name']} - {item['name']}"
            for item in items if item.get("artists")
        ]

    if "/playlist/" in link:
        result = []
        results = sp.playlist_items(link, limit=100)
        for item in results.get("items", []):
            track = item.get("track")
            if track and track.get("artists"):
                result.append(
                    f"{track['artists'][0]['name']} - {track['name']}"
                )
        return result

    raise RuntimeError(
        "Link Spotify không được hỗ trợ. Dùng link track, album hoặc playlist."
    )


# ==================== AUTO NEXT (BÀI GỢI Ý) ====================

def find_related(video_id, title, played: set):
    """Tìm bài gợi ý giống YouTube autoplay.

    Ưu tiên YouTube Mix của bài vừa phát; nếu không có thì tìm theo tên bài.
    Bỏ qua bài đã phát (played) và video quá dài (livestream, mix hàng giờ).
    """
    opts = {
        "quiet": True,
        "no_warnings": True,
        "extract_flat": "in_playlist",
        "playlistend": 25,
        **COOKIE_OPTS,
    }
    sources = []
    if video_id:
        sources.append(
            f"https://www.youtube.com/watch?v={video_id}&list=RD{video_id}"
        )
    if title:
        sources.append(f"ytsearch10:{title}")

    for index, src in enumerate(sources):
        try:
            with yt_dlp.YoutubeDL(opts) as ydl:
                info = ydl.extract_info(src, download=False)
        except Exception as exc:
            print("Không tìm được bài gợi ý:", exc)
            continue

        entries = [e for e in (info or {}).get("entries") or [] if e]
        # Kết quả tìm theo tên: bỏ kết quả đầu vì thường là chính bài vừa phát
        if src.startswith("ytsearch"):
            entries = entries[1:]

        for entry in entries:
            vid = entry.get("id")
            if not vid or vid in played:
                continue
            duration = entry.get("duration")
            if duration and duration > AUTO_MAX_SECONDS:
                continue
            return {"id": vid, "url": f"https://www.youtube.com/watch?v={vid}"}

    return None


# ==================== NOW PLAYING MENU ====================

def current_position(gid: int) -> float:
    """Vị trí phát hiện tại, có tính phần thời gian đã tạm dừng."""
    position = play_positions.get(gid, 0.0)
    started = play_started_at.get(gid)
    if started is not None:
        position += max(0.0, time.monotonic() - started)
    return position


def mark_track_paused(gid: int):
    if gid in play_started_at:
        play_positions[gid] = current_position(gid)
        play_started_at.pop(gid, None)


def mark_track_resumed(gid: int):
    if gid not in play_started_at:
        play_started_at[gid] = time.monotonic()


async def clear_menu(gid: int):
    """Xóa hẳn menu của bài cũ để không để lại nút không còn dùng được."""
    msg = now_playing_msg.pop(gid, None)
    if msg:
        try:
            await msg.delete()
        except Exception:
            try:
                await msg.edit(view=None)
            except Exception:
                pass


def build_now_playing_embed(data: dict, gid: int, auto: bool = False) -> discord.Embed:
    embed = discord.Embed(
        title=data["title"][:250],
        url=data.get("page"),
        color=discord.Color.blurple(),
    )
    embed.add_field(name="⏱️ Thời lượng", value=fmt_duration(data.get("duration")))
    embed.add_field(name="👤 Kênh", value=(data.get("uploader") or "?")[:100])
    embed.add_field(name="🔊 Âm lượng", value=f"{int(round(volumes[gid] * 100))}%")
    if data.get("thumbnail"):
        embed.set_thumbnail(url=data["thumbnail"])
    if auto:
        embed.set_footer(text="🔁 Tự động phát bài tiếp theo")
    return embed


class SeekPositionSelect(discord.ui.Select):
    """Chọn nhanh mốc tua theo phần trăm, không cần nhập thời gian."""

    def __init__(self, duration):
        self.duration = int(duration) if duration else None
        options = []
        if self.duration and self.duration > 1:
            seen = set()
            for percent in (0, 10, 25, 50, 75, 90):
                second = min(int(self.duration * percent / 100), self.duration - 1)
                if second in seen:
                    continue
                seen.add(second)
                stamp = fmt_duration(second) if second else "0:00"
                options.append(discord.SelectOption(
                    label=f"{percent}% · {stamp}",
                    value=str(second),
                    description=f"Tua đến khoảng {percent}% bài hát",
                ))
        if not options:
            options = [discord.SelectOption(label="Không hỗ trợ tua bài này", value="0")]
        super().__init__(
            placeholder="🎯 Tua đến đoạn muốn nghe…",
            min_values=1,
            max_values=1,
            options=options,
            row=2,
            disabled=not bool(self.duration and self.duration > 1),
        )

    async def callback(self, inter: discord.Interaction):
        await seek_interaction(inter, int(self.values[0]))


class NowPlayingView(discord.ui.View):
    """Menu điều khiển hiện dưới tin nhắn 'Đang phát'."""

    def __init__(self, gid: int, embed: discord.Embed, duration=None):
        super().__init__(timeout=None)
        self.gid = gid
        self.embed = embed
        self.add_item(SeekPositionSelect(duration))

    async def interaction_check(self, inter: discord.Interaction) -> bool:
        vc = inter.guild.voice_client
        if not vc or not inter.user.voice or inter.user.voice.channel != vc.channel:
            await inter.response.send_message(
                "🎧 Hãy vào cùng kênh thoại với bot để điều khiển.", ephemeral=True
            )
            return False
        return True

    @discord.ui.button(emoji="⏮️", label="Quay lại", style=discord.ButtonStyle.secondary, row=0)
    async def prev_btn(self, inter: discord.Interaction, button: discord.ui.Button):
        await do_return(inter)

    @discord.ui.button(emoji="⏸️", label="Tạm dừng", style=discord.ButtonStyle.primary, row=0)
    async def pause_btn(self, inter: discord.Interaction, button: discord.ui.Button):
        vc = inter.guild.voice_client
        if vc.is_playing():
            vc.pause()
            mark_track_paused(self.gid)
            button.emoji, button.label = "▶️", "Tiếp tục"
        elif vc.is_paused():
            vc.resume()
            mark_track_resumed(self.gid)
            button.emoji, button.label = "⏸️", "Tạm dừng"
        auto_paused.discard(self.gid)  # Người dùng đã tự quyết định, không tự tiếp tục nữa
        await inter.response.edit_message(view=self)

    @discord.ui.button(emoji="⏭️", label="Skip", style=discord.ButtonStyle.primary, row=0)
    async def skip_btn(self, inter: discord.Interaction, button: discord.ui.Button):
        vc = inter.guild.voice_client
        if vc.is_playing() or vc.is_paused():
            vc.stop()  # after callback sẽ gọi play_next
        await inter.response.defer()

    async def _change_volume(self, inter: discord.Interaction, delta: int):
        gid = self.gid
        percent = max(1, min(400, int(round(volumes[gid] * 100)) + delta))
        volumes[gid] = percent / 100.0

        vc = inter.guild.voice_client
        if vc and isinstance(vc.source, discord.PCMVolumeTransformer):
            vc.source.volume = volumes[gid]

        self.embed.set_field_at(2, name="🔊 Âm lượng", value=f"{percent}%")
        await inter.response.edit_message(embed=self.embed, view=self)

    @discord.ui.button(emoji="🔉", label="-10%", style=discord.ButtonStyle.secondary, row=1)
    async def vol_down_btn(self, inter: discord.Interaction, button: discord.ui.Button):
        await self._change_volume(inter, -10)

    @discord.ui.button(emoji="🔊", label="+10%", style=discord.ButtonStyle.secondary, row=1)
    async def vol_up_btn(self, inter: discord.Interaction, button: discord.ui.Button):
        await self._change_volume(inter, +10)

    @discord.ui.button(emoji="⭐", label="Yêu thích", style=discord.ButtonStyle.success, row=1)
    async def fav_btn(self, inter: discord.Interaction, button: discord.ui.Button):
        data = now_data.get(self.gid)
        if not data or not data.get("page"):
            return await inter.response.send_message(
                "❌ Không lưu được bài này vào yêu thích.", ephemeral=True
            )

        favs = favorites[inter.user.id]
        existing = next((f for f in favs if f["url"] == data["page"]), None)
        if existing:
            favs.remove(existing)
            text = f"💔 Đã bỏ **{data['title'][:100]}** khỏi yêu thích."
        else:
            favs.append({"title": data["title"], "url": data["page"]})
            text = (
                f"⭐ Đã thêm **{data['title'][:100]}** vào yêu thích. "
                "Dùng `/favorites` để xem và phát."
            )
        await inter.response.send_message(text, ephemeral=True)

    @discord.ui.button(label="⏪ -15 giây", style=discord.ButtonStyle.secondary, row=3)
    async def seek_back_btn(self, inter: discord.Interaction, button: discord.ui.Button):
        target = max(0, int(current_position(self.gid) - 15))
        await seek_interaction(inter, target)

    @discord.ui.button(label="+15 giây ⏩", style=discord.ButtonStyle.secondary, row=3)
    async def seek_forward_btn(self, inter: discord.Interaction, button: discord.ui.Button):
        target = int(current_position(self.gid) + 15)
        await seek_interaction(inter, target)


# ==================== KÊNH THOẠI TRỐNG: TẠM DỪNG / TIẾP TỤC ====================

def listener_count(channel) -> int:
    """Số người thật đang ở trong kênh thoại (không tính bot).

    Dùng voice_states thay vì channel.members, vì members chỉ có người đã nằm
    trong bộ nhớ đệm thành viên (bot này không bật members intent).
    """
    me = bot.user.id if bot.user else None
    count = 0
    for user_id in channel.voice_states:
        if user_id == me:
            continue
        member = channel.guild.get_member(user_id)
        if member is not None and member.bot:
            continue
        count += 1
    return count


async def refresh_listening(guild: discord.Guild):
    """Không còn ai trong kênh -> tạm dừng (bot vẫn ở lại). Có người quay lại -> tiếp tục."""
    gid = guild.id
    vc = guild.voice_client
    if not vc or not vc.is_connected():
        return

    if listener_count(vc.channel) == 0:
        # Chỉ tự tạm dừng khi bài đang phát; bài người dùng đã tạm dừng thì để nguyên
        if vc.is_playing():
            vc.pause()
            mark_track_paused(gid)
            auto_paused.add(gid)
            print(f"[{gid}] Kênh thoại trống: tạm dừng, bot vẫn ở lại.")
        return

    if gid in auto_paused:
        auto_paused.discard(gid)
        if vc.is_paused():
            vc.resume()
            mark_track_resumed(gid)
            print(f"[{gid}] Có người quay lại: tiếp tục phát.")

    if gid in waiting_for_listener:
        waiting_for_listener.discard(gid)
        await play_next(guild)


# ==================== PLAY NEXT ====================

async def play_next(guild: discord.Guild, channel=None, retries: int = 0):
    """Phát bài kế tiếp: hàng đợi -> danh sách nhạc (ngẫu nhiên) -> bài gợi ý liên quan."""
    gid = guild.id
    vc = guild.voice_client
    if gid in stopping or not vc or vc.is_playing() or vc.is_paused():
        return

    if channel is None:
        channel = play_channels.get(gid)

    if channel is None:
        return

    await clear_menu(gid)

    # Kênh thoại đang trống: không phát cho không ai nghe, chờ có người vào lại
    if listener_count(vc.channel) == 0:
        waiting_for_listener.add(gid)
        return
    waiting_for_listener.discard(gid)

    q = queues[gid]
    auto_id = None  # id video nếu bài này do bot tự chọn

    if q:
        query = q.pop(0)
    elif autoplay[gid] and music_lists[gid]:
        choices = list(music_lists[gid])
        previous = current_song.get(gid)

        # Tránh phát trùng bài hiện tại nếu danh sách có nhiều lựa chọn
        if len(choices) > 1 and previous in choices:
            choices.remove(previous)

        query = random.choice(choices)
    elif autoplay[gid]:
        # Hết hàng đợi và không có danh sách nhạc: tự mở bài liên quan như YouTube
        seed = now_data.get(gid) or {}
        loop = asyncio.get_running_loop()
        found = await loop.run_in_executor(
            None, find_related,
            seed.get("yt_id"), seed.get("title"), set(recent_ids[gid]),
        )
        if not found:
            return
        query, auto_id = found["url"], found["id"]
    else:
        return

    loop = asyncio.get_running_loop()
    try:
        data = await loop.run_in_executor(None, extract, query)
    except Exception as exc:
        if auto_id:
            recent_ids[gid].append(auto_id)  # Không chọn lại bài lỗi này
            if retries < 2:
                return await play_next(guild, channel, retries + 1)
        print(f"Lỗi lấy bài {query[:80]!r}: {exc}")
        reason = str(exc)
        if "Sign in to confirm" in reason or "cookies" in reason.lower():
            reason = (
                "YouTube đang chặn IP của server và đòi đăng nhập. "
                "Cần thêm cookies cho bot (Secret File cookies.txt trên Render)."
            )
        try:
            await channel.send(f"❌ Không phát được `{query[:80]}`: {reason[:200]}")
        except Exception:
            pass
        if auto_id:
            return  # Bài tự chọn lỗi nhiều lần thì dừng, không thử mãi
        # Thử bài tiếp theo nếu bài này lỗi
        return await play_next(guild, channel)

    # Trong lúc tìm bài, người dùng có thể đã bắt đầu phát bài khác
    if not vc.is_connected() or vc.is_playing() or vc.is_paused():
        queues[gid].insert(0, query)
        return

    # Hoặc mọi người đã rời kênh trong lúc tìm bài: giữ bài lại, chờ có người về
    if listener_count(vc.channel) == 0:
        queues[gid].insert(0, query)
        waiting_for_listener.add(gid)
        return

    current_song[gid] = query
    now_data[gid] = data
    titles[query] = data["title"]
    history[gid].append(query)
    history[gid] = history[gid][-100:]
    if data.get("yt_id"):
        recent_ids[gid].append(data["yt_id"])
        recent_ids[gid] = recent_ids[gid][-100:]

    try:
        audio = discord.FFmpegPCMAudio(data["url"], **FFMPEG_OPTS)
        source = discord.PCMVolumeTransformer(
            audio, volume=volumes[gid]
        )
        vc.play(source, after=make_after_callback(guild, channel, gid))
        play_positions[gid] = 0.0
        play_started_at[gid] = time.monotonic()
    except Exception as exc:
        print("Không thể phát:", exc)
        return await play_next(guild, channel)

    try:
        embed = build_now_playing_embed(data, gid, auto=bool(auto_id))
        now_playing_msg[gid] = await channel.send(
            embed=embed, view=NowPlayingView(gid, embed, data.get("duration"))
        )
    except Exception as exc:
        print("Không gửi được menu (thiếu quyền Embed Links?):", exc)


def make_after_callback(guild: discord.Guild, channel, gid: int):
    """Callback chung cho kết thúc bài; bỏ qua callback do tua/dừng bot."""
    def after(error):
        if error:
            print("Lỗi phát nhạc:", error)
        if gid in seeking or gid in stopping:
            return
        try:
            asyncio.run_coroutine_threadsafe(play_next(guild, channel), bot.loop)
        except Exception as exc:
            print("Không lên lịch được bài tiếp theo:", exc)
    return after


async def seek_to(guild: discord.Guild, channel, target: int) -> int:
    """Khởi động lại stream tại giây đích bằng FFmpeg -ss."""
    gid = guild.id
    vc = guild.voice_client
    data = now_data.get(gid)
    if not vc or not vc.is_connected():
        raise RuntimeError("Bot chưa ở trong kênh thoại.")
    if not data or not data.get("url"):
        raise RuntimeError("Không có bài hát để tua.")
    if not vc.is_playing() and not vc.is_paused():
        raise RuntimeError("Hiện không có bài đang phát để tua.")
    duration = data.get("duration")
    if not duration or int(duration) < 2:
        raise RuntimeError("Bài này không có thời lượng xác định nên không thể tua.")

    target = max(0, min(int(target), int(duration) - 1))
    was_paused = vc.is_paused()
    seeking.add(gid)
    try:
        if vc.is_playing() or vc.is_paused():
            vc.stop()
            # Đợi callback của nguồn cũ chạy xong khi cờ seeking vẫn đang bật.
            await asyncio.sleep(0.25)

        ffmpeg_opts = dict(FFMPEG_OPTS)
        ffmpeg_opts["before_options"] = f"-ss {target} " + ffmpeg_opts["before_options"]
        audio = discord.FFmpegPCMAudio(data["url"], **ffmpeg_opts)
        source = discord.PCMVolumeTransformer(audio, volume=volumes[gid])
        vc.play(source, after=make_after_callback(guild, channel, gid))
        play_positions[gid] = float(target)
        if was_paused:
            vc.pause()
            play_started_at.pop(gid, None)
        else:
            play_started_at[gid] = time.monotonic()
        return target
    finally:
        # Giữ cờ thêm một chút để callback của vc.stop không phát nhầm bài kế tiếp.
        await asyncio.sleep(0.25)
        seeking.discard(gid)


async def seek_interaction(inter: discord.Interaction, target: int):
    await inter.response.defer(ephemeral=True, thinking=True)
    try:
        actual = await seek_to(inter.guild, inter.channel, target)
        await inter.followup.send(f"⏩ Đã tua đến **{fmt_duration(actual)}**.", ephemeral=True)
    except Exception as exc:
        await inter.followup.send(f"❌ Không tua được: {str(exc)[:180]}", ephemeral=True)


# ==================== DISCORD BOT ====================

class MusicCommandTree(app_commands.CommandTree):
    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        # Ghi nhớ đúng kênh đã sử dụng lệnh để dọn tin nhắn cũ tại kênh đó.
        if interaction.guild_id and interaction.channel:
            command_channels[interaction.guild_id] = interaction.channel
        return True


class MusicBot(discord.Client):
    def __init__(self):
        super().__init__(intents=discord.Intents.default())
        self.tree = MusicCommandTree(self)
        self.cleanup_task = None

    async def setup_hook(self):
        await self.tree.sync()
        if self.cleanup_task is None:
            self.cleanup_task = asyncio.create_task(self.cleanup_old_messages_loop())

    async def cleanup_old_messages_loop(self):
        """Định kỳ xóa tin nhắn cũ do chính bot gửi trong các kênh đã dùng lệnh."""
        await self.wait_until_ready()
        while not self.is_closed():
            await asyncio.sleep(MESSAGE_CLEANUP_INTERVAL_SECONDS)
            if not self.user:
                continue
            cutoff = discord.utils.utcnow() - timedelta(seconds=BOT_MESSAGE_TTL_SECONDS)
            for gid, channel in list(command_channels.items()):
                if not channel or not hasattr(channel, "history"):
                    continue
                active_menu = now_playing_msg.get(gid)
                keep_id = active_menu.id if active_menu else None
                try:
                    async for message in channel.history(limit=200, before=cutoff):
                        if message.author.id != self.user.id or message.id == keep_id:
                            continue
                        try:
                            await message.delete()
                            await asyncio.sleep(0.1)
                        except discord.NotFound:
                            pass
                        except discord.Forbidden:
                            print(f"Không có quyền xóa tin nhắn cũ tại kênh {channel.id}.")
                            break
                        except discord.HTTPException as exc:
                            print(f"Không xóa được tin nhắn {message.id}: {exc}")
                except discord.Forbidden:
                    print(f"Không có quyền đọc lịch sử tin nhắn tại kênh {channel.id}.")
                except discord.HTTPException as exc:
                    print(f"Lỗi dọn lịch sử kênh {channel.id}: {exc}")

    async def on_voice_state_update(self, member, before, after):
        vc = member.guild.voice_client
        if not vc or not vc.is_connected():
            return
        # Chỉ quan tâm khi có người vào/ra kênh của bot, hoặc chính bot bị chuyển kênh
        if member.id != self.user.id and vc.channel not in (before.channel, after.channel):
            return
        await refresh_listening(member.guild)


bot = MusicBot()


@bot.tree.error
async def on_app_command_error(inter: discord.Interaction, error: app_commands.AppCommandError):
    """Lệnh nào bị lỗi cũng trả lời người dùng và ghi vào log."""
    print(f"Lỗi lệnh /{inter.command.name if inter.command else '?'}: {error!r}")
    msg = "❌ Có lỗi khi chạy lệnh này, hãy thử lại."
    try:
        if inter.response.is_done():
            await inter.followup.send(msg, ephemeral=True)
        else:
            await inter.response.send_message(msg, ephemeral=True)
    except Exception:
        pass


# ==================== /PLAY ====================

@bot.tree.command(name="play", description="Phát nhạc từ link hoặc tên bài hát")
@app_commands.describe(query="Link YouTube/SoundCloud/Spotify hoặc tên bài hát")
@app_commands.guild_only()
async def play(inter: discord.Interaction, query: str):
    if not inter.user.voice or not inter.user.voice.channel:
        return await inter.response.send_message(
            "🎧 Hãy vào kênh thoại trước.", ephemeral=True
        )

    await inter.response.defer()
    try:
        vc = inter.guild.voice_client
        if vc is None:
            vc = await inter.user.voice.channel.connect()
        elif not vc.is_connected():
            vc = await inter.user.voice.channel.connect()
        elif vc.channel != inter.user.voice.channel:
            await vc.move_to(inter.user.voice.channel)

        play_channels[inter.guild.id] = inter.channel

        if "open.spotify.com" in query:
            loop = asyncio.get_running_loop()
            items = await loop.run_in_executor(None, spotify_to_queries, query)
        else:
            items = [query]

        if not items:
            return await inter.followup.send("❌ Không tìm thấy bài hát.")

        queues[inter.guild.id].extend(items)
        await inter.followup.send(
            f"➕ Đã thêm **{len(items)} bài** vào hàng đợi."
        )

        if not vc.is_playing() and not vc.is_paused():
            await play_next(inter.guild, inter.channel)

    except Exception as exc:
        await inter.followup.send(f"❌ Có lỗi: {str(exc)[:200]}")


# ==================== /VOLUME ====================

@bot.tree.command(name="volume", description="Chỉnh âm lượng từ 1% đến 400%")
@app_commands.describe(level="Nhập âm lượng từ 1 đến 400")
@app_commands.guild_only()
async def volume(inter: discord.Interaction, level: app_commands.Range[int, 1, 400]):
    gid = inter.guild_id
    volumes[gid] = level / 100.0
    vc = inter.guild.voice_client

    if vc and vc.source and isinstance(vc.source, discord.PCMVolumeTransformer):
        vc.source.volume = volumes[gid]

    await inter.response.send_message(f"🔊 Đã chỉnh âm lượng thành **{level}%**.")


# ==================== /RETURN ====================

async def do_return(inter: discord.Interaction):
    """Quay lại bài trước (dùng cho lệnh /return và nút trên menu)."""
    gid = inter.guild_id
    vc = inter.guild.voice_client
    songs = history[gid]

    if not vc or not vc.is_connected():
        return await inter.response.send_message(
            "❌ Bot chưa ở trong kênh thoại.", ephemeral=True
        )
    if len(songs) < 2:
        return await inter.response.send_message(
            "❌ Chưa có bài trước để quay lại.", ephemeral=True
        )
    if gid in return_pending:
        return await inter.response.send_message(
            "⏳ Đang xử lý lệnh quay lại.", ephemeral=True
        )

    # Bài áp chót là bài trước bài đang phát
    previous = songs[-2]
    return_pending.add(gid)

    # Bỏ bài đang phát và bài trước khỏi lịch sử; bài trước sẽ được ghi lại khi phát,
    # nhờ vậy bấm quay lại nhiều lần vẫn lùi dần được
    songs.pop()
    songs.pop()

    # Đưa bài trước lên đầu hàng đợi, giữ nguyên những bài chờ khác
    queues[gid].insert(0, previous)
    play_channels[gid] = inter.channel

    await inter.response.send_message(
        f"⏮️ Đang quay lại bài: **{titles.get(previous, previous)[:150]}**"
    )
    try:
        if vc.is_playing() or vc.is_paused():
            vc.stop()  # after callback sẽ gọi play_next
        else:
            await play_next(inter.guild, inter.channel)
    finally:
        return_pending.discard(gid)


@bot.tree.command(name="return", description="Quay lại bài hát trước đó")
@app_commands.guild_only()
async def return_song(inter: discord.Interaction):
    await do_return(inter)


# ==================== /SKIP-TO ====================


def queue_item_title(query: str) -> str:
    """Tên dễ đọc cho bài đang chờ; ưu tiên tiêu đề đã được bot phân giải."""
    return titles.get(query, query).strip() or query


class SkipToSelect(discord.ui.Select):
    def __init__(self, parent_view):
        self.parent_view = parent_view
        start = parent_view.page * 25
        page_items = parent_view.snapshot[start:start + 25]
        options = []
        for index, item in enumerate(page_items, start=start):
            label = f"{index + 1}. {queue_item_title(item)}"[:100]
            options.append(discord.SelectOption(
                label=label,
                value=str(index),
                description=f"Phát từ vị trí {index + 1} trong hàng đợi"[:100],
            ))
        super().__init__(
            placeholder="Chọn bài muốn chuyển đến…",
            min_values=1,
            max_values=1,
            options=options,
            row=0,
        )

    async def callback(self, inter: discord.Interaction):
        await self.parent_view.choose(inter, int(self.values[0]))


class SkipToView(discord.ui.View):
    """Danh sách chọn bài skip-to, hỗ trợ hàng đợi dài hơn 25 bài."""

    def __init__(self, guild: discord.Guild, channel, snapshot: list[str]):
        super().__init__(timeout=180)
        self.guild = guild
        self.channel = channel
        self.gid = guild.id
        self.snapshot = list(snapshot)
        self.page = 0
        self.message = None
        self.refresh_items()

    def build_embed(self) -> discord.Embed:
        total = len(self.snapshot)
        page_count = max(1, (total + 24) // 25)
        start = self.page * 25
        lines = [
            f"**{i + 1}.** {queue_item_title(item)[:115]}"
            for i, item in enumerate(self.snapshot[start:start + 25], start=start)
        ]
        embed = discord.Embed(
            title=f"📜 Hàng đợi nhạc ({total} bài)",
            description="\n".join(lines) if lines else "Hàng đợi đang trống.",
            color=discord.Color.blurple(),
        )
        embed.set_footer(text=f"Trang {self.page + 1}/{page_count} • Chọn bài trong menu bên dưới")
        return embed

    def refresh_items(self):
        self.clear_items()
        if not self.snapshot:
            return
        self.add_item(SkipToSelect(self))
        page_count = max(1, (len(self.snapshot) + 24) // 25)
        previous_button = discord.ui.Button(
            label="◀ Trang trước", style=discord.ButtonStyle.secondary,
            row=1, disabled=self.page <= 0,
        )
        next_button = discord.ui.Button(
            label="Trang sau ▶", style=discord.ButtonStyle.secondary,
            row=1, disabled=self.page >= page_count - 1,
        )
        previous_button.callback = self.previous_page
        next_button.callback = self.next_page
        self.add_item(previous_button)
        self.add_item(next_button)

    async def previous_page(self, inter: discord.Interaction):
        self.page = max(0, self.page - 1)
        self.refresh_items()
        await inter.response.edit_message(embed=self.build_embed(), view=self)

    async def next_page(self, inter: discord.Interaction):
        page_count = max(1, (len(self.snapshot) + 24) // 25)
        self.page = min(page_count - 1, self.page + 1)
        self.refresh_items()
        await inter.response.edit_message(embed=self.build_embed(), view=self)

    async def choose(self, inter: discord.Interaction, index: int):
        q = queues[self.gid]
        if list(q) != self.snapshot:
            self.snapshot = list(q)
            self.page = min(self.page, max(0, (len(self.snapshot) - 1) // 25))
            self.refresh_items()
            if self.snapshot:
                return await inter.response.edit_message(
                    content="⚠️ Hàng đợi vừa thay đổi. Đây là danh sách mới; hãy chọn lại bài.",
                    embed=self.build_embed(), view=self,
                )
            return await inter.response.edit_message(
                content="📜 Hàng đợi hiện đã trống.", embed=None, view=None,
            )

        vc = self.guild.voice_client
        if not vc or not vc.is_connected():
            return await inter.response.send_message(
                "❌ Bot không còn ở trong kênh thoại.", ephemeral=True,
            )
        if index < 0 or index >= len(q):
            return await inter.response.send_message(
                "❌ Vị trí này không còn trong hàng đợi.", ephemeral=True,
            )

        selected = q[index]
        del q[:index]  # Đưa bài được chọn lên đầu, bỏ các bài đứng trước nó.
        play_channels[self.gid] = self.channel
        await inter.response.edit_message(
            content=f"⏭️ Đang chuyển đến **{queue_item_title(selected)[:180]}** (vị trí {index + 1}).",
            embed=None,
            view=None,
        )
        if vc.is_playing() or vc.is_paused():
            vc.stop()  # Callback sẽ phát bài đã được đưa lên đầu hàng đợi.
        else:
            await play_next(self.guild, self.channel)

    async def on_timeout(self):
        if self.message:
            try:
                await self.message.delete()
            except Exception:
                try:
                    await self.message.edit(view=None)
                except Exception:
                    pass


@bot.tree.command(
    name="skip-to",
    description="Hiện hàng đợi và chọn bài muốn chuyển đến",
)
@app_commands.guild_only()
async def skip_to(inter: discord.Interaction):
    gid = inter.guild_id
    vc = inter.guild.voice_client
    q = queues[gid]

    if not vc or not vc.is_connected():
        return await inter.response.send_message(
            "❌ Bot chưa ở trong kênh thoại.", ephemeral=True,
        )
    if not q:
        return await inter.response.send_message(
            "📜 Hàng đợi đang trống. Dùng `/play` để thêm bài trước.", ephemeral=True,
        )

    view = SkipToView(inter.guild, inter.channel, list(q))
    await inter.response.send_message(
        "Chọn bài trong danh sách để bot bỏ qua các bài đứng trước và phát bài đó:",
        embed=view.build_embed(),
        view=view,
        ephemeral=True,
    )
    view.message = await inter.original_response()


# ==================== /PAUSE ====================

@bot.tree.command(name="pause", description="Tạm dừng nhạc")
@app_commands.guild_only()
async def pause(inter: discord.Interaction):
    vc = inter.guild.voice_client
    if vc and vc.is_playing():
        vc.pause()
        mark_track_paused(inter.guild_id)
        auto_paused.discard(inter.guild_id)
        await inter.response.send_message("⏸️ Đã tạm dừng.")
    else:
        await inter.response.send_message(
            "❌ Không có nhạc để tạm dừng.", ephemeral=True
        )


# ==================== /RESUME ====================

@bot.tree.command(name="resume", description="Tiếp tục phát nhạc")
@app_commands.guild_only()
async def resume(inter: discord.Interaction):
    vc = inter.guild.voice_client
    if vc and vc.is_paused():
        vc.resume()
        mark_track_resumed(inter.guild_id)
        auto_paused.discard(inter.guild_id)
        await inter.response.send_message("▶️ Tiếp tục phát nhạc.")
    else:
        await inter.response.send_message(
            "❌ Không có nhạc đang tạm dừng.", ephemeral=True
        )


# ==================== /QUEUE ====================

@bot.tree.command(name="queue", description="Xem danh sách nhạc chờ")
@app_commands.guild_only()
async def queue_cmd(inter: discord.Interaction):
    q = queues[inter.guild_id]
    if not q:
        return await inter.response.send_message(
            "📜 Hàng đợi đang trống.", ephemeral=True
        )

    text = "\n".join(f"{i + 1}. {item[:80]}" for i, item in enumerate(q[:15]))
    more = f"\n... và {len(q) - 15} bài nữa" if len(q) > 15 else ""
    await inter.response.send_message(f"📜 **Hàng đợi:**\n{text}{more}")


# ==================== /FAVORITES ====================

async def connect_voice(inter: discord.Interaction):
    """Vào (hoặc chuyển sang) kênh thoại của người dùng."""
    vc = inter.guild.voice_client
    if vc is None or not vc.is_connected():
        vc = await inter.user.voice.channel.connect()
    elif vc.channel != inter.user.voice.channel:
        await vc.move_to(inter.user.voice.channel)
    return vc


class FavoritesView(discord.ui.View):
    def __init__(self):
        super().__init__(timeout=300)

    @discord.ui.button(label="▶️ Phát tất cả", style=discord.ButtonStyle.success)
    async def play_all(self, inter: discord.Interaction, button: discord.ui.Button):
        favs = favorites[inter.user.id]
        if not favs:
            return await inter.response.send_message(
                "⭐ Danh sách yêu thích đang trống.", ephemeral=True
            )
        if not inter.user.voice or not inter.user.voice.channel:
            return await inter.response.send_message(
                "🎧 Hãy vào kênh thoại trước.", ephemeral=True
            )

        await inter.response.defer(ephemeral=True)
        try:
            gid = inter.guild_id
            vc = await connect_voice(inter)
            play_channels[gid] = inter.channel
            queues[gid].extend(f["url"] for f in favs)
            await inter.followup.send(
                f"✅ Đã xếp **{len(favs)} bài** yêu thích vào hàng đợi.",
                ephemeral=True,
            )
            if not vc.is_playing() and not vc.is_paused():
                await play_next(inter.guild, inter.channel)
        except Exception as exc:
            await inter.followup.send(f"❌ Lỗi: {str(exc)[:200]}", ephemeral=True)

    @discord.ui.button(label="🗑️ Xóa hết", style=discord.ButtonStyle.danger)
    async def clear_all(self, inter: discord.Interaction, button: discord.ui.Button):
        favorites[inter.user.id].clear()
        await inter.response.send_message(
            "🗑️ Đã xóa toàn bộ bài yêu thích của bạn.", ephemeral=True
        )


@bot.tree.command(name="favorites", description="Xem và phát các bài yêu thích của bạn")
@app_commands.guild_only()
async def favorites_cmd(inter: discord.Interaction):
    favs = favorites[inter.user.id]
    if not favs:
        return await inter.response.send_message(
            "⭐ Bạn chưa có bài yêu thích nào. Bấm ⭐ trên menu khi bot đang phát để thêm.",
            ephemeral=True,
        )

    shown = favs[:20]
    text = "\n".join(f"{i + 1}. {f['title'][:80]}" for i, f in enumerate(shown))
    more = f"\n... và {len(favs) - 20} bài nữa" if len(favs) > 20 else ""
    await inter.response.send_message(
        f"⭐ **Bài yêu thích của bạn ({len(favs)}):**\n{text}{more}",
        view=FavoritesView(),
        ephemeral=True,
    )


# ==================== PRIVATE MUSIC LIST UI ====================

class AddSongsModal(discord.ui.Modal, title="Thêm danh sách nhạc"):
    songs = discord.ui.TextInput(
        label="Tên bài hát hoặc link (mỗi dòng một bài)",
        style=discord.TextStyle.paragraph,
        placeholder="Tên bài 1\nTên bài 2\nTên bài 3",
        max_length=4000,
        required=True,
    )

    async def on_submit(self, inter: discord.Interaction):
        gid = inter.guild_id
        if gid is None:
            return await inter.response.send_message(
                "Lệnh này chỉ dùng trong server.", ephemeral=True
            )

        added = [line.strip() for line in self.songs.value.splitlines() if line.strip()]
        music_lists[gid].extend(added)
        await inter.response.send_message(
            f"✅ Đã thêm **{len(added)} bài** vào danh sách nhạc.\n"
            f"Tổng cộng: **{len(music_lists[gid])} bài**.",
            ephemeral=True,
        )


class MusicListView(discord.ui.View):
    def __init__(self):
        super().__init__(timeout=300)

    @discord.ui.button(label="➕ Thêm bài", style=discord.ButtonStyle.primary)
    async def add_songs(self, inter: discord.Interaction, button: discord.ui.Button):
        await inter.response.send_modal(AddSongsModal())

    @discord.ui.button(label="📜 Xem danh sách", style=discord.ButtonStyle.secondary)
    async def show_songs(self, inter: discord.Interaction, button: discord.ui.Button):
        songs = music_lists[inter.guild_id]
        if not songs:
            return await inter.response.send_message(
                "Danh sách nhạc đang trống. Bấm **Thêm bài** để bắt đầu.",
                ephemeral=True,
            )

        page_size = 30
        pages = [
            songs[i:i + page_size] for i in range(0, len(songs), page_size)
        ]
        page_text = "\n".join(
            f"{i + 1}. {song[:90]}"
            for i, song in enumerate(pages[0])
        )
        await inter.response.send_message(
            f"📜 **Danh sách nhạc (1/{len(pages)} trang):**\n{page_text}",
            ephemeral=True,
        )

    @discord.ui.button(label="▶️ Xếp phát lần lượt", style=discord.ButtonStyle.success)
    async def queue_list(self, inter: discord.Interaction, button: discord.ui.Button):
        gid = inter.guild_id
        songs = music_lists[gid]
        if not songs:
            return await inter.response.send_message(
                "❌ Hãy thêm bài hát vào danh sách trước.", ephemeral=True
            )
        if not inter.user.voice or not inter.user.voice.channel:
            return await inter.response.send_message(
                "🎧 Hãy vào kênh thoại trước.", ephemeral=True
            )

        await inter.response.defer(ephemeral=True)
        try:
            vc = inter.guild.voice_client
            if vc is None:
                vc = await inter.user.voice.channel.connect()
            elif not vc.is_connected():
                vc = await inter.user.voice.channel.connect()
            elif vc.channel != inter.user.voice.channel:
                await vc.move_to(inter.user.voice.channel)

            play_channels[gid] = inter.channel
            queues[gid].extend(songs)
            await inter.followup.send(
                f"✅ Đã xếp **{len(songs)} bài** phát lần lượt.",
                ephemeral=True,
            )
            if not vc.is_playing() and not vc.is_paused():
                await play_next(inter.guild, inter.channel)
        except Exception as exc:
            await inter.followup.send(f"❌ Lỗi: {str(exc)[:200]}", ephemeral=True)

    @discord.ui.button(label="🔀 Bật/tắt tự động phát tiếp", style=discord.ButtonStyle.secondary)
    async def toggle_random(self, inter: discord.Interaction, button: discord.ui.Button):
        gid = inter.guild_id
        autoplay[gid] = not autoplay[gid]
        state = "BẬT" if autoplay[gid] else "TẮT"
        await inter.response.send_message(
            f"🔀 Tự động phát tiếp: **{state}**.\n"
            "Khi hàng đợi hết, bot sẽ chọn ngẫu nhiên từ danh sách nhạc nếu có, "
            "nếu không sẽ tự mở bài gợi ý liên quan như YouTube.",
            ephemeral=True,
        )

    @discord.ui.button(label="🗑️ Xóa danh sách", style=discord.ButtonStyle.danger)
    async def clear_list(self, inter: discord.Interaction, button: discord.ui.Button):
        music_lists[inter.guild_id].clear()
        await inter.response.send_message(
            "🗑️ Đã xóa danh sách nhạc đã lưu trong bộ nhớ.",
            ephemeral=True,
        )


@bot.tree.command(name="musiclist", description="Mở bảng quản lý danh sách nhạc riêng tư")
@app_commands.guild_only()
async def musiclist(inter: discord.Interaction):
    await inter.response.send_message(
        "🎵 **QUẢN LÝ DANH SÁCH NHẠC**\n"
        "Thêm nhiều bài, xem danh sách, xếp phát lần lượt hoặc bật/tắt tự động phát tiếp.\n"
        "Bảng này chỉ mình bạn nhìn thấy.",
        view=MusicListView(),
        ephemeral=True,
    )


# ==================== /STOP ====================

@bot.tree.command(name="stop", description="Dừng nhạc, xóa hàng đợi và thoát kênh")
@app_commands.guild_only()
async def stop(inter: discord.Interaction):
    gid = inter.guild_id
    queues[gid].clear()
    # Trả lời ngay: ngắt kênh thoại có thể lâu hơn 3 giây, Discord sẽ báo "không phản hồi"
    await inter.response.send_message("⏹️ Đang dừng nhạc và thoát kênh thoại...")
    stopping.add(gid)  # Chặn play_next tự phát bài mới trong lúc đang dừng
    vc = inter.guild.voice_client

    try:
        if vc:
            if vc.is_playing() or vc.is_paused():
                vc.stop()
            await vc.disconnect()
    finally:
        stopping.discard(gid)

    current_song.pop(gid, None)
    now_data.pop(gid, None)
    play_positions.pop(gid, None)
    play_started_at.pop(gid, None)
    auto_paused.discard(gid)
    waiting_for_listener.discard(gid)
    await clear_menu(gid)

# ==================== /SEARCH ====================

def search_youtube(query: str, limit: int = 10) -> list[dict]:
    """Tìm trên YouTube, chỉ lấy thông tin cơ bản (nhanh, không tải gì)."""
    opts = {"quiet": True, "no_warnings": True, "extract_flat": True, **COOKIE_OPTS}
    with yt_dlp.YoutubeDL(opts) as ydl:
        info = ydl.extract_info(f"ytsearch{limit}:{query}", download=False)

    results = []
    for e in (info or {}).get("entries") or []:
        if not e or not e.get("id"):
            continue
        results.append({
            "title": e.get("title") or "Không rõ tên",
            "url": f"https://www.youtube.com/watch?v={e['id']}",
            "channel": e.get("channel") or e.get("uploader") or "?",
            "duration": e.get("duration"),
        })
    return results


def fmt_duration(sec) -> str:
    if sec is None:
        return "--:--"
    sec = int(sec)
    h, rest = divmod(sec, 3600)
    m, s = divmod(rest, 60)
    return f"{h}:{m:02d}:{s:02d}" if h else f"{m}:{s:02d}"


class SearchSelect(discord.ui.Select):
    def __init__(self, results: list[dict]):
        self.results = results
        options = [
            discord.SelectOption(
                label=f"{i + 1}. {r['title']}"[:100],
                description=f"{r['channel']} • {fmt_duration(r['duration'])}"[:100],
                value=str(i),
            )
            for i, r in enumerate(results)
        ]
        super().__init__(placeholder="Chọn bài để phát...", options=options)

    async def callback(self, inter: discord.Interaction):
        gid = inter.guild_id
        chosen = self.results[int(self.values[0])]

        if not inter.user.voice or not inter.user.voice.channel:
            return await inter.response.send_message(
                "🎧 Hãy vào kênh thoại trước.", ephemeral=True
            )

        await inter.response.defer()
        try:
            vc = inter.guild.voice_client
            if vc is None or not vc.is_connected():
                vc = await inter.user.voice.channel.connect()
            elif vc.channel != inter.user.voice.channel:
                await vc.move_to(inter.user.voice.channel)

            play_channels[gid] = inter.channel
            titles[chosen["url"]] = chosen["title"]
            queues[gid].append(chosen["url"])
            self.view.stop()
            await inter.edit_original_response(
                content=f"✅ Đã chọn: **{chosen['title']}**", view=None
            )
            if not vc.is_playing() and not vc.is_paused():
                await play_next(inter.guild, inter.channel)
        except Exception as exc:
            await inter.followup.send(f"❌ Lỗi: {str(exc)[:200]}", ephemeral=True)


class SearchView(discord.ui.View):
    def __init__(self, results: list[dict], author_id: int):
        super().__init__(timeout=60)
        self.author_id = author_id
        self.message = None
        self.add_item(SearchSelect(results))

    async def interaction_check(self, inter: discord.Interaction) -> bool:
        if inter.user.id != self.author_id:
            await inter.response.send_message(
                "Chỉ người gọi lệnh mới chọn được.", ephemeral=True
            )
            return False
        return True

    async def on_timeout(self):
        if self.message:
            try:
                await self.message.delete()
            except Exception:
                try:
                    await self.message.edit(content="⌛ Hết thời gian chọn.", view=None)
                except Exception:
                    pass


@bot.tree.command(name="search", description="Tìm bài trên YouTube rồi chọn bài để phát")
@app_commands.describe(query="Tên bài hát hoặc từ khóa tìm kiếm")
@app_commands.guild_only()
async def search(inter: discord.Interaction, query: str):
    if not inter.user.voice or not inter.user.voice.channel:
        return await inter.response.send_message(
            "🎧 Hãy vào kênh thoại trước.", ephemeral=True
        )

    await inter.response.defer()
    loop = asyncio.get_running_loop()
    try:
        results = await loop.run_in_executor(None, search_youtube, query)
    except Exception as exc:
        return await inter.followup.send(f"❌ Không tìm được: {str(exc)[:200]}")

    if not results:
        return await inter.followup.send("❌ Không có kết quả nào.")

    lines = "\n".join(
        f"**{i + 1}.** {r['title'][:80]} — {r['channel'][:30]} `{fmt_duration(r['duration'])}`"
        for i, r in enumerate(results)
    )
    view = SearchView(results, inter.user.id)
    view.message = await inter.followup.send(
        f"🔎 Kết quả cho **{query[:80]}**:\n{lines}", view=view, wait=True
    )

# ==================== RUN BOT (RENDER) ====================

async def start_web_server():
    """Web server nhỏ để Render nhận diện service và để UptimeRobot ping."""
    async def health(request):
        status = "online" if bot.is_ready() else "connecting"
        return web.Response(text=f"Music bot is running (discord: {status})")

    app = web.Application()
    app.router.add_get("/", health)
    runner = web.AppRunner(app)
    await runner.setup()
    port = int(os.environ.get("PORT", 10000))
    await web.TCPSite(runner, "0.0.0.0", port).start()
    print(f"Web server đang chạy ở cổng {port}")


async def main():
    if not TOKEN:
        raise ValueError("Không tìm thấy biến môi trường DISCORD_TOKEN trên Render.")

    await start_web_server()

    delay = 60
    while True:
        try:
            await bot.login(TOKEN)
            break
        except discord.LoginFailure:
            raise  # Token sai thì thử lại cũng vô ích
        except discord.HTTPException as exc:
            if exc.status != 429:
                raise
            print(f"Discord đang chặn IP của server (429). Thử lại sau {delay} giây...")
            await asyncio.sleep(delay)
            delay = min(delay * 2, 900)

    try:
        await bot.connect(reconnect=True)
    finally:
        await bot.close()


if __name__ == "__main__":
    asyncio.run(main())
