#include <stdarg.h>
#include <string.h>
#include <errno.h>

#include "mednafen/mednafen.h"
#include "mednafen/mempatcher.h"
#include "mednafen/git.h"
#include "mednafen/general.h"
#include "mednafen/md5.h"
#include "mednafen/gba/GBA.h"
#include "mednafen/gba/Globals.h"
#include "libretro.h"

static MDFNGI *game;
MDFNGI *MDFNGameInfo = NULL;

struct retro_perf_callback perf_cb;
retro_get_cpu_features_t perf_get_cpu_features_cb = NULL;
retro_log_printf_t log_cb;
static retro_video_refresh_t video_cb;
static retro_audio_sample_t audio_cb;
static retro_audio_sample_batch_t audio_batch_cb;
static retro_environment_t environ_cb;
static retro_input_poll_t input_poll_cb;
static retro_input_state_t input_state_cb;
static retro_set_rumble_state_t rumble_cb;

static bool rumble_state = false;
static bool rumble_isrunning = false;
static int rumble = 0;
static const int rumble_frames = 4; // delays turning off rumble for N frames;

static uint8 sensorDarkness = 0xE8;
static uint8 sensorDarknessLevel = 0;

static double last_sound_rate;

static MDFN_PixelFormat last_pixel_format;

static MDFN_Surface *surf;

static bool failed_init;

static void hookup_ports(bool force);

static bool initial_ports_hookup = false;

std::string retro_base_directory;
std::string retro_base_name;
std::string retro_save_directory;

/* Workaround for broken-by-design GBA save semantics. */
uint8_t libretro_save_buf[0x20000 + 0x2000];
static unsigned libretro_save_size = sizeof(libretro_save_buf);
bool use_mednafen_save_method = false;

static void set_basename(const char *path)
{
   const char *base = strrchr(path, '/');
   if (!base)
      base = strrchr(path, '\\');

   if (base)
      retro_base_name = base + 1;
   else
      retro_base_name = path;

   retro_base_name = retro_base_name.substr(0, retro_base_name.find_last_of('.'));
}

#define MEDNAFEN_CORE_NAME_MODULE "gba"
#define MEDNAFEN_CORE_NAME "Beetle GBA"
#define MEDNAFEN_CORE_VERSION "v0.9.36"
#define MEDNAFEN_CORE_EXTENSIONS "gba|agb|bin"
#define MEDNAFEN_CORE_TIMING_FPS 59.73
#define MEDNAFEN_CORE_GEOMETRY_BASE_W (game->nominal_width)
#define MEDNAFEN_CORE_GEOMETRY_BASE_H (game->nominal_height)
#define MEDNAFEN_CORE_GEOMETRY_MAX_W 240
#define MEDNAFEN_CORE_GEOMETRY_MAX_H 160
#define MEDNAFEN_CORE_GEOMETRY_ASPECT_RATIO (3.0 / 2.0)
#define FB_WIDTH 240
#define FB_HEIGHT 160

#define FB_MAX_HEIGHT FB_HEIGHT

static bool scan_area(const uint8_t *data, unsigned size)
{
   for (unsigned i = 0; i < size; i++)
      if (data[i] != 0xff)
         return true;

   return false;
}

static void adjust_save_ram()
{
   if (scan_area(libretro_save_buf, 512) &&
         !scan_area(libretro_save_buf + 512, sizeof(libretro_save_buf) - 512))
   {
      libretro_save_size = 512;
      if (log_cb)
         log_cb(RETRO_LOG_INFO, "Detecting EEprom 8kbit\n");
   }
   else if (scan_area(libretro_save_buf, 0x2000) &&
         !scan_area(libretro_save_buf + 0x2000, sizeof(libretro_save_buf) - 0x2000))
   {
      libretro_save_size = 0x2000;
      if (log_cb)
         log_cb(RETRO_LOG_INFO, "Detecting EEprom 64kbit\n");
   }

   else if (scan_area(libretro_save_buf, 0x10000) &&
         !scan_area(libretro_save_buf + 0x10000, sizeof(libretro_save_buf) - 0x10000))
   {
      libretro_save_size = 0x10000;
      if (log_cb)
         log_cb(RETRO_LOG_INFO, "Detecting Flash 512kbit\n");
   }
   else if (scan_area(libretro_save_buf, 0x20000) &&
         !scan_area(libretro_save_buf + 0x20000, sizeof(libretro_save_buf) - 0x20000))
   {
      libretro_save_size = 0x20000;
      if (log_cb)
         log_cb(RETRO_LOG_INFO, "Detecting Flash 1Mbit\n");
   }
   else if (log_cb)
      log_cb(RETRO_LOG_INFO, "Did not detect any particular SRAM type.\n");

   /*if (libretro_save_size == 512 || libretro_save_size == 0x2000)
      eepromData = libretro_save_buf;
   else if (libretro_save_size == 0x10000 || libretro_save_size == 0x20000)
      flashSaveMemory = libretro_save_buf;*/
}

static void check_system_specs(void)
{
   unsigned level = 0;
   environ_cb(RETRO_ENVIRONMENT_SET_PERFORMANCE_LEVEL, &level);
}

void retro_init(void)
{
   memset(libretro_save_buf, 0xFF, sizeof(libretro_save_buf));
   struct retro_log_callback log;
   if (environ_cb(RETRO_ENVIRONMENT_GET_LOG_INTERFACE, &log))
      log_cb = log.log;
   else
      log_cb = NULL;

   const char *dir = NULL;

   if (environ_cb(RETRO_ENVIRONMENT_GET_SYSTEM_DIRECTORY, &dir) && dir)
   {
      retro_base_directory = dir;
      // Make sure that we don't have any lingering slashes, etc, as they break Windows.
      size_t last = retro_base_directory.find_last_not_of("/\\");
      if (last != std::string::npos)
         last++;

      retro_base_directory = retro_base_directory.substr(0, last);
   }
   else
   {
      /* TODO: Add proper fallback */
      if (log_cb)
         log_cb(RETRO_LOG_WARN, "System directory is not defined. Fallback on using same dir as ROM for system directory later ...\n");
      failed_init = true;
   }

   if (environ_cb(RETRO_ENVIRONMENT_GET_SAVE_DIRECTORY, &dir) && dir)
   {
      // If save directory is defined use it, otherwise use system directory
      retro_save_directory = *dir ? dir : retro_base_directory;
      // Make sure that we don't have any lingering slashes, etc, as they break Windows.
      size_t last = retro_save_directory.find_last_not_of("/\\");
      if (last != std::string::npos)
         last++;

      retro_save_directory = retro_save_directory.substr(0, last);
   }
   else
   {
      /* TODO: Add proper fallback */
      if (log_cb)
         log_cb(RETRO_LOG_WARN, "Save directory is not defined. Fallback on using SYSTEM directory ...\n");
      retro_save_directory = retro_base_directory;
   }

#if defined(WANT_16BPP) && defined(FRONTEND_SUPPORTS_RGB565)
   enum retro_pixel_format rgb565 = RETRO_PIXEL_FORMAT_RGB565;
   if (environ_cb(RETRO_ENVIRONMENT_SET_PIXEL_FORMAT, &rgb565) && log_cb)
      log_cb(RETRO_LOG_INFO, "Frontend supports RGB565 - will use that instead of XRGB1555.\n");
#endif

   if (environ_cb(RETRO_ENVIRONMENT_GET_PERF_INTERFACE, &perf_cb))
      perf_get_cpu_features_cb = perf_cb.get_cpu_features;
   else
      perf_get_cpu_features_cb = NULL;

   retro_rumble_interface rumble;
   if (environ_cb(RETRO_ENVIRONMENT_GET_RUMBLE_INTERFACE, &rumble))
      rumble_cb = rumble.set_rumble_state;
   else
      rumble_cb = NULL;

   check_system_specs();
}

void retro_reset(void)
{
   DoSimpleCommand(MDFN_MSC_RESET);
}

bool retro_load_game_special(unsigned, const struct retro_game_info *, size_t)
{
   return false;
}

static void check_variables(bool startup)
{
   struct retro_variable var = {0};

   var.key = "gba_hle";

   if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value && startup)
   {
      if (strcmp(var.value, "enabled") == 0)
         setting_gba_hle = 1;
      else if (strcmp(var.value, "disabled") == 0)
         setting_gba_hle = 0;
   }

   var.key = "gba_use_mednafen_save_method";

   if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value && startup)
   {
      if (strcmp(var.value, "mednafen") == 0)
         use_mednafen_save_method = true;
      else if (strcmp(var.value, "libretro") == 0)
         use_mednafen_save_method = false;
   }
}

#define MAX_PLAYERS 1
#define MAX_BUTTONS 11
static uint16_t input_buf;

static void hookup_ports(bool force)
{
   if (initial_ports_hookup && !force)
      return;

   // Possible endian bug ...
   SetInput(0, "gamepad", &input_buf);

   initial_ports_hookup = true;
}

bool retro_load_game(const struct retro_game_info *info)
{
   if (!info || failed_init)
      return false;

   struct retro_input_descriptor desc[] = {
      { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_LEFT,  "D-Pad Left" },
      { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_UP,    "D-Pad Up" },
      { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_DOWN,  "D-Pad Down" },
      { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_RIGHT, "D-Pad Right" },
      { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_B,     "B" },
      { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_A,     "A" },
      { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_L,     "L" },
      { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_R,     "R" },
      { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_SELECT, "Select" },
      { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_START, "Start" },
      { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_L2,     "Solar Level Decrease" },
      { 0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_R2,     "Solar Level Increase" },

      { 0 },
   };

   environ_cb(RETRO_ENVIRONMENT_SET_INPUT_DESCRIPTORS, desc);

#ifdef WANT_32BPP
   enum retro_pixel_format fmt = RETRO_PIXEL_FORMAT_XRGB8888;
   if (!environ_cb(RETRO_ENVIRONMENT_SET_PIXEL_FORMAT, &fmt))
   {
      if (log_cb)
         log_cb(RETRO_LOG_ERROR, "Pixel format XRGB8888 not supported by platform, cannot use %s.\n", MEDNAFEN_CORE_NAME);
      return false;
   }
#endif

   set_basename(info->path);

   check_variables(true);

   game = MDFNI_LoadGame(MEDNAFEN_CORE_NAME_MODULE, (const uint8_t *)info->data, info->size);
   if (!game)
      return false;

   MDFN_PixelFormat pix_fmt(MDFN_COLORSPACE_RGB, 16, 8, 0, 24);
   last_pixel_format = MDFN_PixelFormat();

   surf = new MDFN_Surface(NULL, FB_WIDTH, FB_HEIGHT, FB_WIDTH, pix_fmt);

   hookup_ports(true);

   struct retro_memory_descriptor descs[7];
   struct retro_memory_map retromap;

   memset(descs, 0, sizeof(descs));

   descs[0].ptr    = internalRAM;    // Internal working RAM
   descs[0].start  = 0x03000000;
   descs[0].len    = 0x8000;
   descs[0].select = 0xFF000000;

   descs[1].ptr    = workRAM;        // Working RAM
   descs[1].start  = 0x02000000;
   descs[1].len    = 0x40000;
   descs[1].select = 0xFF000000;

   // TODO: if SRAM is flash, use start=0 addrspace="S" instead
   descs[2].ptr    = flashSaveMemory;  // Save RAM
   descs[2].start  = 0x0E000000;
   descs[2].len    = flashSize;
   descs[2].select = 0;

   descs[3].ptr    = vram;           // VRAM
   descs[3].start  = 0x06000000;
   descs[3].len    = 0x20000;
   descs[3].select = 0xFF000000;

   descs[4].ptr    = paletteRAM;     // Palettes
   descs[4].start  = 0x05000000;
   descs[4].len    = 0x400;
   descs[4].select = 0xFF000000;

   descs[5].ptr    = oam;            // OAM
   descs[5].start  = 0x07000000;
   descs[5].len    = 0x400;
   descs[5].select = 0xFF000000;

   descs[6].ptr    = ioMem;          // I/O
   descs[6].start  = 0x04000000;
   descs[6].len    = 0x400;
   descs[6].select = 0;

   retromap.descriptors       = descs;
   retromap.num_descriptors   = sizeof(descs) / sizeof(*descs);

   environ_cb(RETRO_ENVIRONMENT_SET_MEMORY_MAPS, &retromap);

   bool retroarchievement = true;
   environ_cb(RETRO_ENVIRONMENT_SET_SUPPORT_ACHIEVEMENTS, &retroarchievement);

   return game;
}

void retro_unload_game()
{
   if (!game)
      return;

   MDFNI_CloseGame();
}

static void systemUpdateSolarSensor(int v)
{
    int value = 0;
    switch (v) {
    case 1:  value = 0x06; break;
    case 2:  value = 0x0E; break;
    case 3:  value = 0x18; break;
    case 4:  value = 0x20; break;
    case 5:  value = 0x28; break;
    case 6:  value = 0x38; break;
    case 7:  value = 0x48; break;
    case 8:  value = 0x60; break;
    case 9:  value = 0x78; break;
    case 10: value = 0x98; break;
    default: break;
    }

    sensorDarkness = 0xE8 - value;
}

static void update_input(void)
{
   input_buf = 0;
   size_t map_size = 10;
   static unsigned map[] = {
      RETRO_DEVICE_ID_JOYPAD_A, //A button
      RETRO_DEVICE_ID_JOYPAD_B, //B button
      RETRO_DEVICE_ID_JOYPAD_SELECT,
      RETRO_DEVICE_ID_JOYPAD_START,
      RETRO_DEVICE_ID_JOYPAD_RIGHT,
      RETRO_DEVICE_ID_JOYPAD_LEFT,
      RETRO_DEVICE_ID_JOYPAD_UP,
      RETRO_DEVICE_ID_JOYPAD_DOWN,
      RETRO_DEVICE_ID_JOYPAD_R,
      RETRO_DEVICE_ID_JOYPAD_L,
   };

   for (unsigned i = 0; i < map_size; i++)
      input_buf |= map[i] != -1u &&
         input_state_cb(0, RETRO_DEVICE_JOYPAD, 0, map[i]) ? (1 << i) : 0;

#ifdef MSB_FIRST
   union {
      uint8_t b[2];
      uint16_t s;
   } u;
   u.s = input_buf;
   input_buf = u.b[0] | u.b[1] << 8;
#endif
   
   if ((hardware & SENSOR_RUMBLE) && rumble_cb)
   {
      // Do rumble frames
      if (rumble_state == true && rumble_isrunning == false)
      {
         // Only do rumble callback if not running already
         rumble_cb(0, RETRO_RUMBLE_WEAK, 0xffff);
         rumble_cb(0, RETRO_RUMBLE_STRONG, 0xffff);
         rumble_isrunning = true;
         rumble = rumble_frames;
      }
      else if (rumble && rumble_isrunning)
      {
         // Make sure we disable rumble after Nth frames
         rumble--;
         if (!rumble)
         {
            rumble_cb(0, RETRO_RUMBLE_WEAK, 0);
            rumble_cb(0, RETRO_RUMBLE_STRONG, 0);
            rumble_isrunning = false;
            rumble_state = false;
         }
      }
   }

   if (hardware & SENSOR_SOLAR) {
      static bool buttonpressed = false;
      if (buttonpressed) {
         buttonpressed = input_state_cb(0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_R2) ||
            input_state_cb(0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_L2);
      } else {
         if (input_state_cb(0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_R2)) {
            sensorDarknessLevel++;
            if (sensorDarknessLevel > 10)
               sensorDarknessLevel = 10;
            systemUpdateSolarSensor(sensorDarknessLevel);
            buttonpressed = true;
         } else if (input_state_cb(0, RETRO_DEVICE_JOYPAD, 0, RETRO_DEVICE_ID_JOYPAD_L2)) {
            if (sensorDarknessLevel)
               sensorDarknessLevel--;
            systemUpdateSolarSensor(sensorDarknessLevel);
            buttonpressed = true;
         }
      }
   }
}

void retro_run()
{
   input_poll_cb();

   update_input();

   static int16_t sound_buf[0x10000];
   static MDFN_Rect rects[FB_MAX_HEIGHT];
   rects[0].w = ~0;

   EmulateSpecStruct spec = {0};
   spec.surface = surf;
   spec.SoundRate = 44100;
   spec.SoundBuf = sound_buf;
   spec.LineWidths = rects;
   spec.SoundBufMaxSize = sizeof(sound_buf) / 2;
   spec.SoundVolume = 1.0;
   spec.soundmultiplier = 1.0;
   spec.SoundBufSize = 0;
   spec.VideoFormatChanged = false;
   spec.SoundFormatChanged = false;

   if (memcmp(&last_pixel_format, &spec.surface->format, sizeof(MDFN_PixelFormat)))
   {
      spec.VideoFormatChanged = true;

      last_pixel_format = spec.surface->format;
   }

   if (spec.SoundRate != last_sound_rate)
   {
      spec.SoundFormatChanged = true;
      last_sound_rate = spec.SoundRate;
   }

   Emulate(&spec);

   unsigned width  = spec.DisplayRect.w;
   unsigned height = spec.DisplayRect.h;

#if defined(WANT_32BPP)
   const uint32_t *pix = surf->pixels;
   video_cb(pix, width, height, FB_WIDTH << 2);
#elif defined(WANT_16BPP)
   const uint16_t *pix = surf->pixels16;
   video_cb(pix, width, height, FB_WIDTH << 1);
#endif

   audio_batch_cb(spec.SoundBuf, spec.SoundBufSize);

   bool updated = false;
   if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE_UPDATE, &updated) && updated)
     check_variables(false);
}

void retro_get_system_info(struct retro_system_info *info)
{
   memset(info, 0, sizeof(*info));
   info->library_name     = MEDNAFEN_CORE_NAME;
#ifndef GIT_VERSION
#define GIT_VERSION ""
#endif
   info->library_version  = MEDNAFEN_CORE_VERSION GIT_VERSION;
   info->need_fullpath    = false;
   info->valid_extensions = MEDNAFEN_CORE_EXTENSIONS;
   info->block_extract    = false;
}

void retro_get_system_av_info(struct retro_system_av_info *info)
{
   memset(info, 0, sizeof(*info));
   info->timing.fps            = MEDNAFEN_CORE_TIMING_FPS;
   info->timing.sample_rate    = 44100;
   info->geometry.base_width   = MEDNAFEN_CORE_GEOMETRY_BASE_W;
   info->geometry.base_height  = MEDNAFEN_CORE_GEOMETRY_BASE_H;
   info->geometry.max_width    = MEDNAFEN_CORE_GEOMETRY_MAX_W;
   info->geometry.max_height   = MEDNAFEN_CORE_GEOMETRY_MAX_H;
   info->geometry.aspect_ratio = MEDNAFEN_CORE_GEOMETRY_ASPECT_RATIO;
}

void retro_deinit()
{
   delete surf;
   surf = NULL;
}

unsigned retro_get_region(void)
{
   return RETRO_REGION_NTSC; // FIXME: Regions for other cores.
}

unsigned retro_api_version(void)
{
   return RETRO_API_VERSION;
}

void retro_set_controller_port_device(unsigned in_port, unsigned device)
{
}

void retro_set_environment(retro_environment_t cb)
{
   environ_cb = cb;

   static const struct retro_variable vars[] = {
      { "gba_hle", "HLE bios emulation (Restart); enabled|disabled" },
      { "gba_use_mednafen_save_method", "Save method (Restart); mednafen|libretro" },
      { NULL, NULL },
   };
   cb(RETRO_ENVIRONMENT_SET_VARIABLES, (void*)vars);
}

void retro_set_audio_sample(retro_audio_sample_t cb)
{
   audio_cb = cb;
}

void retro_set_audio_sample_batch(retro_audio_sample_batch_t cb)
{
   audio_batch_cb = cb;
}

void retro_set_input_poll(retro_input_poll_t cb)
{
   input_poll_cb = cb;
}

void retro_set_input_state(retro_input_state_t cb)
{
   input_state_cb = cb;
}

void retro_set_video_refresh(retro_video_refresh_t cb)
{
   video_cb = cb;
}

static size_t serialize_size;

size_t retro_serialize_size(void)
{
   StateMem st;

   st.data           = NULL;
   st.loc            = 0;
   st.len            = 0;
   st.malloced       = 0;
   st.initial_malloc = 0;

   if (!MDFNSS_SaveSM(&st, 0, 0, NULL, NULL, NULL))
      return 0;

   free(st.data);

   return serialize_size = st.len;
}

bool retro_serialize(void *data, size_t size)
{
   StateMem st;
   bool ret          = false;
   uint8_t *_dat     = (uint8_t*)malloc(size);

   if (!_dat)
      return false;

   /* Mednafen can realloc the buffer so we need to ensure this is safe. */
   st.data           = _dat;
   st.loc            = 0;
   st.len            = 0;
   st.malloced       = size;
   st.initial_malloc = 0;

   ret = MDFNSS_SaveSM(&st, 0, 0, NULL, NULL, NULL);

   memcpy(data, st.data, size);
   free(st.data);

   return ret;
}

bool retro_unserialize(const void *data, size_t size)
{
   StateMem st;
   memset(&st, 0, sizeof(st));
   st.data = (uint8_t*)data;
   st.len  = size;

   return MDFNSS_LoadSM(&st, 0, 0);
}

void *retro_get_memory_data(unsigned type)
{
   if (type == RETRO_MEMORY_SAVE_RAM)
   {
      if (!use_mednafen_save_method)
         return libretro_save_buf;
   }
   else if ( type == RETRO_MEMORY_SYSTEM_RAM )
   {
      return workRAM ;
   }

   return NULL;
}

size_t retro_get_memory_size(unsigned type)
{
   if (type == RETRO_MEMORY_SAVE_RAM)
   {
      if (!use_mednafen_save_method)
         return libretro_save_size;
   }
   else if ( type == RETRO_MEMORY_SYSTEM_RAM )
   {
      return 0x40000 ;
   }

   return 0;
}

void retro_cheat_reset(void)
{}

void retro_cheat_set(unsigned, bool, const char *)
{}

#ifdef _WIN32
static void sanitize_path(std::string &path)
{
   size_t size = path.size();
   for (size_t i = 0; i < size; i++)
      if (path[i] == '/')
         path[i] = '\\';
}
#endif

// Use a simpler approach to make sure that things go right for libretro.
std::string MDFN_MakeFName(MakeFName_Type type, int id1, const char *cd1)
{
   char slash;
#ifdef _WIN32
   slash = '\\';
#else
   slash = '/';
#endif
   std::string ret;
   switch (type)
   {
      case MDFNMKF_SAV:
         ret = retro_save_directory +slash + retro_base_name +
            std::string(".") +
#ifndef _XBOX
         md5_context::asciistr(MDFNGameInfo->MD5, 0) + std::string(".") +
#endif
            std::string(cd1);
         break;
      case MDFNMKF_FIRMWARE:
         ret = retro_base_directory + slash + std::string(cd1);
#ifdef _WIN32
         sanitize_path(ret); // Because Windows path handling is mongoloid.
#endif
         break;
      default:
         break;
   }

   if (log_cb)
      log_cb(RETRO_LOG_INFO, "MDFN_MakeFName: %s\n\n", ret.c_str());
   return ret;
}

void MDFND_DispMessage(unsigned char *str)
{
   if (log_cb)
      log_cb(RETRO_LOG_INFO, "%s\n", str);
}

void MDFND_Message(const char *str)
{
   if (log_cb)
      log_cb(RETRO_LOG_INFO, "%s", str);
}

void MDFND_PrintError(const char* err)
{
   if (log_cb)
      log_cb(RETRO_LOG_ERROR, "%s\n", err);
}

/* forward declarations */
extern void MDFND_DispMessage(unsigned char *str);

void MDFN_DispMessage(const char *format, ...)
{
 va_list ap;
 va_start(ap,format);
 char *msg = new char[4096];

 vsnprintf(msg, 4096, format,ap);
 va_end(ap);

 MDFND_DispMessage((UTF8*)msg);
}

void MDFN_ResetMessages(void)
{
 MDFND_DispMessage(NULL);
}

MDFNGI *MDFNI_LoadGame(const char *force_module, const uint8_t *data, size_t size)
{
   MDFNGameInfo = &EmulatedGBA;
   MDFN_indent(2);

   if(Load(data, size) <= 0)
   {
      MDFN_indent(-2);
      MDFNGameInfo = NULL;
      return(0);
   }

   MDFN_LoadGameCheats(NULL);
   MDFNMP_InstallReadPatches();

   //MDFN_ResetMessages();   // Save state, status messages, etc.

   MDFN_indent(-2);

   return(MDFNGameInfo);
}

void MDFNI_CloseGame(void)
{
   if(!MDFNGameInfo)
      return;

   MDFN_FlushGameCheats(0);

   CloseGame();

   MDFNMP_Kill();

   MDFNGameInfo = NULL;
}

static int curindent = 0;

void MDFN_indent(int indent)
{
 curindent += indent;
}

static uint8 lastchar = 0;

void MDFN_printf(const char *format, ...)
{
   char *format_temp;
   char *temp;
   unsigned int x, newlen;

   va_list ap;
   va_start(ap,format);


   // First, determine how large our format_temp buffer needs to be.
   uint8 lastchar_backup = lastchar; // Save lastchar!
   for(newlen=x=0;x<strlen(format);x++)
   {
      if(lastchar == '\n' && format[x] != '\n')
      {
         int y;
         for(y=0;y<curindent;y++)
            newlen++;
      }
      newlen++;
      lastchar = format[x];
   }

   format_temp = (char *)malloc(newlen + 1); // Length + NULL character, duh

   // Now, construct our format_temp string
   lastchar = lastchar_backup; // Restore lastchar
   for(newlen=x=0;x<strlen(format);x++)
   {
      if(lastchar == '\n' && format[x] != '\n')
      {
         int y;
         for(y=0;y<curindent;y++)
            format_temp[newlen++] = ' ';
      }
      format_temp[newlen++] = format[x];
      lastchar = format[x];
   }

   format_temp[newlen] = 0;

   temp = new char[4096];
   vsnprintf(temp, 4096, format_temp, ap);
   free(format_temp);

   MDFND_Message(temp);
   free(temp);

   va_end(ap);
}

void MDFN_PrintError(const char *format, ...)
{
 char *temp;

 va_list ap;

 va_start(ap, format);

 temp = new char[4096];
 vsnprintf(temp, 4096, format, ap);
 MDFND_PrintError(temp);
 free(temp);

 va_end(ap);
}

void MDFN_DebugPrintReal(const char *file, const int line, const char *format, ...)
{
 char *temp;

 va_list ap;

 va_start(ap, format);

 temp = new char[4096];
 vsnprintf(temp, 4096, format, ap);
 fprintf(stderr, "%s:%d  %s\n", file, line, temp);
 free(temp);

 va_end(ap);
}

void systemCartridgeRumble(bool e)
{
   rumble_state = e;
}

uint8 systemGetSensorDarkness()
{
   return sensorDarkness;
}

int systemGetSensorZ()
{
   return 0;
}
