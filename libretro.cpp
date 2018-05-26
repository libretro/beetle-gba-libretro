#include "mednafen/mednafen.h"
#include "mednafen/mempatcher.h"
#include "mednafen/git.h"
#include "mednafen/general.h"
#include "mednafen/md5.h"
#ifdef NEED_DEINTERLACER
#include "mednafen/video/Deinterlacer.h"
#endif
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

static retro_rumble_interface rumble;

static bool overscan;
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

// VisualBoyAdvance - Nintendo Gameboy/GameboyAdvance (TM) emulator.
// Copyright (C) 1999-2003 Forgotten
// Copyright (C) 2005 Forgotten and the VBA development team

// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2, or(at your option)
// any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program; if not, write to the Free Software Foundation,
// Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

#include "mednafen/gba/GBA.h"
#include "mednafen/general.h"
#include "mednafen/file.h"
#include "mednafen/state.h"
#include "mednafen/mempatcher.h"
#include "mednafen/md5.h"
#include "mednafen/gba/GBAinline.h"
#include "mednafen/gba/Globals.h"
#include "mednafen/gba/Gfx.h"
#include "mednafen/gba/eeprom.h"
#include "mednafen/gba/flash.h"
#include "mednafen/gba/Sound.h"
#include "mednafen/gba/sram.h"
#include "mednafen/gba/bios.h"
#include "mednafen/gba/Port.h"

#include "mednafen/gba/arm.h"
#include "mednafen/gba/thumb.h"

#include <stdarg.h>
#include <string.h>
#include <errno.h>

#include "mednafen/FileStream.h"

#include "scrc32.h"

static bool CPUInit(const std::string bios_fn) MDFN_COLD;
static void CPUReset(void) MDFN_COLD;
static void CPUUpdateRender(void);

#define UPDATE_REG(address, value)\
  {\
    WRITE16LE(((uint16 *)&ioMem[address]),value);\
  }\

#ifdef __GNUC__
#define _stricmp strcasecmp
#endif

RTC *GBA_RTC = NULL;

int SWITicks = 0;
int IRQTicks = 0;

int layerEnableDelay = 0;
bool busPrefetch = false;
bool busPrefetchEnable = false;
uint32 busPrefetchCount = 0;
int cpuDmaTicksToUpdate = 0;
int cpuDmaCount = 0;
bool cpuDmaHack = false;
uint32 cpuDmaLast = 0;
int dummyAddress = 0;

bool cpuBreakLoop = false;
int cpuNextEvent = 0;

static bool intState = false;
static bool stopState = false;
static bool holdState = false;
static int holdType = 0;

static bool FlashSizeSet; // Set to TRUE if explicitly set by the user
bool cpuSramEnabled;
bool cpuFlashEnabled;
bool cpuEEPROMEnabled;
bool cpuEEPROMSensorEnabled;

uint32 cpuPrefetch[2];

int cpuTotalTicks = 0;
static int lcdTicks;
uint8 timerOnOffDelay = 0;

GBATimer timers[4];

uint32 dmaSource[4] = {0};
uint32 dmaDest[4] = {0};
void (*renderLine)() = mode0RenderLine;
bool fxOn = false;
bool windowOn = false;

static const int TIMER_TICKS[4] =
{
  0,
  6,
  8,
  10
};

const uint32  objTilesAddress [3] = {0x010000, 0x014000, 0x014000};
const uint8 gamepakRamWaitState[4] = { 4, 3, 2, 8 };
const uint8 gamepakWaitState[4] =  { 4, 3, 2, 8 };
const uint8 gamepakWaitState0[2] = { 2, 1 };
const uint8 gamepakWaitState1[2] = { 4, 1 };
const uint8 gamepakWaitState2[2] = { 8, 1 };
const bool isInRom [16]=
  { false, false, false, false, false, false, false, false,
    true, true, true, true, true, true, false, false };

uint8 memoryWait[16] =
  { 0, 0, 2, 0, 0, 0, 0, 0, 4, 4, 4, 4, 4, 4, 4, 0 };
uint8 memoryWait32[16] =
  { 0, 0, 5, 0, 0, 1, 1, 0, 7, 7, 9, 9, 13, 13, 4, 0 };
uint8 memoryWaitSeq[16] =
  { 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 4, 4, 8, 8, 4, 0 };
uint8 memoryWaitSeq32[16] =
  { 0, 0, 5, 0, 0, 1, 1, 0, 5, 5, 9, 9, 17, 17, 4, 0 };

// The videoMemoryWait constants are used to add some waitstates
// if the opcode access video memory data outside of vblank/hblank
// It seems to happen on only one ticks for each pixel.
// Not used for now (too problematic with current code).
//const uint8 videoMemoryWait[16] =
//  {0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0};


uint8 biosProtected[4];

static const uint32 myROM[] =
{
 #include "mednafen/gba/myrom.h"
};

union SysCM
{
 uint32 v32[65536];
 uint16 v16[65536];
};
static SysCM* systemColorMap = NULL;
static uint8 *CustomColorMap = NULL; // 32768 * 3
static int romSize = 0x2000000;

static INLINE int CPUUpdateTicks()
{
  int cpuLoopTicks = lcdTicks;

  if(timers[0].On && (timers[0].Ticks < cpuLoopTicks)) {
    cpuLoopTicks = timers[0].Ticks;
  }
  if(timers[1].On && !(timers[1].CNT & 4) && (timers[1].Ticks < cpuLoopTicks)) {
    cpuLoopTicks = timers[1].Ticks;
  }
  if(timers[2].On && !(timers[2].CNT & 4) && (timers[2].Ticks < cpuLoopTicks)) {
    cpuLoopTicks = timers[2].Ticks;
  }
  if(timers[3].On && !(timers[3].CNT & 4) && (timers[3].Ticks < cpuLoopTicks)) {
    cpuLoopTicks = timers[3].Ticks;
  }

  if (SWITicks) {
    if (SWITicks < cpuLoopTicks)
        cpuLoopTicks = SWITicks;
  }

  if (IRQTicks) {
    if (IRQTicks < cpuLoopTicks)
        cpuLoopTicks = IRQTicks;
  }
  return cpuLoopTicks;
}

void CPUUpdateWindow0()
{
  int x00 = WIN0H>>8;
  int x01 = WIN0H & 255;

  if(x00 <= x01) {
    for(int i = 0; i < 240; i++) {
      gfxInWin0[i] = (i >= x00 && i < x01);
    }
  } else {
    for(int i = 0; i < 240; i++) {
      gfxInWin0[i] = (i >= x00 || i < x01);
    }
  }
}

void CPUUpdateWindow1()
{
  int x00 = WIN1H>>8;
  int x01 = WIN1H & 255;

  if(x00 <= x01) {
    for(int i = 0; i < 240; i++) {
      gfxInWin1[i] = (i >= x00 && i < x01);
    }
  } else {
    for(int i = 0; i < 240; i++) {
      gfxInWin1[i] = (i >= x00 || i < x01);
    }
  }
}

#define CLEAR_ARRAY(a) \
  {\
    uint32 *array = (a);\
    for(int i = 0; i < 240; i++) {\
      *array++ = 0x80000000;\
    }\
  }\

void CPUUpdateRenderBuffers(bool force)
{
  if(!(layerEnable & 0x0100) || force) {
    CLEAR_ARRAY(line0);
  }
  if(!(layerEnable & 0x0200) || force) {
    CLEAR_ARRAY(line1);
  }
  if(!(layerEnable & 0x0400) || force) {
    CLEAR_ARRAY(line2);
  }
  if(!(layerEnable & 0x0800) || force) {
    CLEAR_ARRAY(line3);
  }
}

static uint16 padbufblah;
static SFORMAT Joy_StateRegs[] =
{
 SFVAR( padbufblah),
 SFEND
};

int StateAction(StateMem *sm, int load, int data_only)
{
 int ret = 1;

 SFORMAT StateRegs[] =
 {
  // Type-cast to uint32* so the macro will work(they really are 32-bit elements, just wrapped up in a union)
  SFARRAY32N((uint32 *)reg, sizeof(reg) / sizeof(reg_pair), "reg"),

  SFVAR(busPrefetch),
  SFVAR(busPrefetchEnable),
  SFVAR(busPrefetchCount),
  SFVAR(cpuDmaHack),
  SFVAR(cpuDmaLast),
  SFVAR(cpuDmaTicksToUpdate),
  SFVAR(cpuDmaCount),
  SFVAR(stopState),
  SFVAR(intState),
  SFVAR(DISPCNT),
  SFVAR(DISPSTAT),
  SFVAR(VCOUNT),
  SFVAR(BG0CNT),
  SFVAR(BG1CNT),
  SFVAR(BG2CNT),
  SFVAR(BG3CNT),


  SFARRAY16(BGHOFS, 4),
  SFARRAY16(BGVOFS, 4),

  SFVAR(BG2PA),
  SFVAR(BG2PB),
  SFVAR(BG2PC),
  SFVAR(BG2PD),
  SFVAR(BG2X_L),
  SFVAR(BG2X_H),
  SFVAR(BG2Y_L),
  SFVAR(BG2Y_H),

  SFVAR(BG3PA),
  SFVAR(BG3PB),
  SFVAR(BG3PC),
  SFVAR(BG3PD),
  SFVAR(BG3X_L),
  SFVAR(BG3X_H),
  SFVAR(BG3Y_L),
  SFVAR(BG3Y_H),
  SFVAR(WIN0H),
  SFVAR(WIN1H),
  SFVAR(WIN0V),
  SFVAR(WIN1V),
  SFVAR(WININ),
  SFVAR(WINOUT),
  SFVAR(MOSAIC),
  SFVAR(BLDMOD),
  SFVAR(COLEV),
  SFVAR(COLY),

  SFARRAY16(DMSAD_L, 4),
  SFARRAY16(DMSAD_H, 4),
  SFARRAY16(DMDAD_L, 4),
  SFARRAY16(DMDAD_H, 4),
  SFARRAY16(DMCNT_L, 4),
  SFARRAY16(DMCNT_H, 4),

  SFVAR(timers[0].D),
  SFVAR(timers[0].CNT),
  SFVAR(timers[1].D),
  SFVAR(timers[1].CNT),
  SFVAR(timers[2].D),
  SFVAR(timers[2].CNT),
  SFVAR(timers[3].D),
  SFVAR(timers[3].CNT),

  SFVAR(P1),
  SFVAR(IE),
  SFVAR(IF),
  SFVAR(IME),

  SFVAR(holdState),
  SFVAR(holdType),
  SFVAR(lcdTicks),

  SFVAR(timers[0].On),
  SFVAR(timers[0].Ticks),
  SFVAR(timers[0].Reload),
  SFVAR(timers[0].ClockReload),

  SFVAR(timers[1].On),
  SFVAR(timers[1].Ticks),
  SFVAR(timers[1].Reload),
  SFVAR(timers[1].ClockReload),

  SFVAR(timers[2].On),
  SFVAR(timers[2].Ticks),
  SFVAR(timers[2].Reload),
  SFVAR(timers[2].ClockReload),

  SFVAR(timers[3].On),
  SFVAR(timers[3].Ticks),
  SFVAR(timers[3].Reload),
  SFVAR(timers[3].ClockReload),

  SFARRAY32(dmaSource, 4),
  SFARRAY32(dmaDest, 4),

  SFVAR(fxOn),
  SFVAR(windowOn),

  SFVAR(N_FLAG),
  SFVAR(C_FLAG),
  SFVAR(Z_FLAG),
  SFVAR(V_FLAG),
  SFVAR(armState),
  SFVAR(armIrqEnable),
  SFVAR(armNextPC),
  SFVAR(armMode),

  SFVAR(cpuSramEnabled),
  SFVAR(cpuFlashEnabled),
  SFVAR(cpuEEPROMEnabled),
  SFVAR(cpuEEPROMSensorEnabled),

  SFEND
 };

 ret &= MDFNSS_StateAction(sm, load, data_only, StateRegs, "MAIN");

 SFORMAT RAMState[] =
 {
  SFARRAY(internalRAM, 0x8000),
  SFARRAY(paletteRAM, 0x400),
  SFARRAY(workRAM, 0x40000),
  SFARRAY(vram, 0x20000),
  SFARRAY(oam, 0x400),
  SFARRAY(ioMem, 0x400),
  SFEND
 };

 ret &= MDFNSS_StateAction(sm, load, data_only, RAMState, "RAM");

 if(cpuEEPROMEnabled)
  ret &= EEPROM_StateAction(sm, load, data_only);

 ret &= GBA_Flash_StateAction(sm, load, data_only);

 if(GBA_RTC)
  ret &= GBA_RTC->StateAction(sm, load, data_only);

 ret &= MDFNSS_StateAction(sm, load, data_only, Joy_StateRegs, "JOY");
 ret &= MDFNGBASOUND_StateAction(sm, load, data_only);

 if(load)
 {
  // set pointers!
  layerEnable = layerSettings & DISPCNT;

  CPUUpdateRender();
  CPUUpdateRenderBuffers(true);
  CPUUpdateWindow0();
  CPUUpdateWindow1();

  if(armState) {
    ARM_PREFETCH;
  } else {
    THUMB_PREFETCH;
  }
  CPUUpdateRegister(0x204, CPUReadHalfWordQuick(0x4000204));
 }
 return(ret);
}

static bool CPUWriteBatteryFile(const char *filename) MDFN_COLD;
static bool CPUWriteBatteryFile(const char *filename)
{
 if(cpuSramEnabled || cpuFlashEnabled)
 {
  if(cpuSramEnabled)
  {
   if(!MDFN_DumpToFile(filename, 6, flashSaveMemory, 0x10000))
    return(0);
  }
  else if(cpuFlashEnabled)
  {
   if(!MDFN_DumpToFile(filename, 6, flashSaveMemory, flashSize))
    return(0);
  }
  return(TRUE);
 }
 return(FALSE);
}

static bool CPUReadBatteryFile(const char *filename) MDFN_COLD;
static bool CPUReadBatteryFile(const char *filename)
{
 FILE *gp = gzopen(filename, "rb");
 long size;

 if(!gp)
  return(FALSE);

 size = 0;
 while(gzgetc(gp) != EOF)
  size++;

 if(size == 512 || size == 0x2000) // Load the file as EEPROM for Mednafen < 0.8.2
 {
  gzclose(gp);

  if(cpuEEPROMEnabled)
  {
   puts("note:  Loading sav file as eeprom data");
   GBA_EEPROM_LoadFile(filename);
  }
  return(FALSE);
 }

 gzseek(gp, 0, SEEK_SET);

 if(size == 0x20000)
 {
  if(gzread(gp, flashSaveMemory, 0x20000) != 0x20000)
  {
   gzclose(gp);
   return(FALSE);
  }
  if(!FlashSizeSet)
  {
   flashSetSize(0x20000);
   FlashSizeSet = TRUE;
  }
 }
 else
 {
  if(gzread(gp, flashSaveMemory, 0x10000) != 0x10000)
  {
   gzclose(gp);
   return(FALSE);
  }
  if(!FlashSizeSet)
  {
   flashSetSize(0x10000);
   FlashSizeSet = TRUE;
  }
 }
 gzclose(gp);
 return(TRUE);
}

static void CPUCleanUp(void) MDFN_COLD;
static void CPUCleanUp(void)
{
 if(rom)
 {
  free(rom);
  rom = NULL;
 }

 if(vram)
 {
  free(vram);
  vram = NULL;
 }

 if(paletteRAM)
 {
  free(paletteRAM);
  paletteRAM = NULL;
 }

 if(internalRAM)
 {
  free(internalRAM);
  internalRAM = NULL;
 }

 if(workRAM)
 {
  free(workRAM);
  workRAM = NULL;
 }

 if(bios)
 {
  free(bios);
  bios = NULL;
 }

 if(pix)
 {
  free(pix);
  pix = NULL;
 }

 if(oam)
 {
  free(oam);
  oam = NULL;
 }

 if(ioMem)
 {
  free(ioMem);
  ioMem = NULL;
 }

 if(systemColorMap)
 {
  free(systemColorMap);
  systemColorMap = NULL;
 }

 MDFNGBASOUND_Kill();

 GBA_Flash_Kill();

 if(GBA_RTC)
 {
  delete GBA_RTC;
  GBA_RTC = NULL;
 }
}

static void CloseGame(void)
{
 if (use_mednafen_save_method)
 {
   GBA_EEPROM_SaveFile(MDFN_MakeFName(MDFNMKF_SAV, 0, "eep").c_str());
   CPUWriteBatteryFile(MDFN_MakeFName(MDFNMKF_SAV, 0, "sav").c_str());
 }

 // Call CPUCleanUp() to deallocate memory AFTER the backup memory is saved.
 CPUCleanUp();
}

static bool LoadCPalette(const char *syspalname, uint8 **ptr, uint32 num_entries) MDFN_COLD;
static bool LoadCPalette(const char *syspalname, uint8 **ptr, uint32 num_entries)
{
 std::string colormap_fn = MDFN_MakeFName(MDFNMKF_PALETTE, 0, syspalname).c_str();

 MDFN_printf(_("Loading custom palette from \"%s\"...\n"),  colormap_fn.c_str());
 MDFN_indent(1);

 *ptr = NULL;
 try
 {
  FileStream fp(colormap_fn.c_str(), FileStream::MODE_READ);

  if(!(*ptr = (uint8 *)malloc(num_entries * 3)))
  {
   MDFN_indent(-1);
   return(false);
  }

  fp.read(*ptr, num_entries * 3);
 }
 catch(MDFN_Error &e)
 {
  if(*ptr)
  {
   free(*ptr);
   *ptr = NULL;
  }

  MDFN_printf(_("Error: %s\n"), e.what());
  MDFN_indent(-1);
  return(e.GetErrno() == ENOENT);        // Return fatal error if it's an error other than the file not being found.
 }
 catch(std::exception &e)
 {
  if(*ptr)
  {
   free(*ptr);
   *ptr = NULL;
  }

  MDFN_printf(_("Error: %s\n"), e.what());
  MDFN_indent(-1);
  return(false);
 }

 MDFN_indent(-1);

 return(true);
}

static void RedoColorMap(const MDFN_PixelFormat &format) MDFN_COLD;
static void RedoColorMap(const MDFN_PixelFormat &format)
{
 for(int x = 0; x < 65536; x++)
 {
  int r, g, b;

  if(CustomColorMap)
  {
   r = CustomColorMap[(x & 0x7FFF) * 3 + 0];
   g = CustomColorMap[(x & 0x7FFF) * 3 + 1];
   b = CustomColorMap[(x & 0x7FFF) * 3 + 2];
  }
  else
  {
   r = (x & 0x1F);
   g = ((x & 0x3E0) >> 5);
   b = ((x & 0x7C00) >> 10);

   if(format.bpp == 16)
   {
    r = (r * 255 + 15) / 31;
    g = (g * 255 + 15) / 31;
    b = (b * 255 + 15) / 31;
   }
   else
   {
    r = (r << 3); // | (r >> 2);
    g = (g << 3); // | (g >> 2);
    b = (b << 3); // | (b >> 2);
   }
  }

  if(format.bpp == 32)
   systemColorMap->v32[x] = format.MakeColor(r, g, b);
  else
   systemColorMap->v16[x] = format.MakeColor(r, g, b);
 }

 #if 0
 for(unsigned i = 0; i < 32; i++)
 {
  printf("%u %u\n", i, format.MakeColor(0, 0, (i * 255 + 15) / 31));
 }
 #endif
}

static int Load(const uint8_t *data, size_t size)
{
  layerSettings = 0xFF00;

  if(!(rom = (uint8 *)malloc(0x2000000)))
   return(0);

  memset(rom, 0xFF, 0x2000000);

  if(!(workRAM = (uint8 *)calloc(1, 0x40000)))
  {
   free(rom);
   return(0);
  }


  {
   uint8 *whereToLoad;

   if(cpuIsMultiBoot)
   {
    whereToLoad = workRAM;
    if(size > 0x40000)
     size = 0x40000;
   }
   else
   {
    whereToLoad = rom;
    if(size > 0x2000000)
     size = 0x2000000;
   }

   memcpy(whereToLoad, data, size);

   md5_context md5;
   md5.starts();
   md5.update(data, size);
   md5.finish(MDFNGameInfo->MD5);

   MDFN_printf(_("ROM:       %dKiB\n"), (size + 1023) / 1024);
   MDFN_printf(_("ROM CRC32: 0x%08x\n"), (unsigned int)crc32(0, data, size));
   MDFN_printf(_("ROM MD5:   0x%s\n"), md5_context::asciistr(MDFNGameInfo->MD5, 0).c_str());

   uint16 *temp = (uint16 *)(rom+((size+1)&~1));
   int i;

   for(i = (size+1)&~1; i < 0x2000000; i+=2)
   {
    WRITE16LE(temp, (i >> 1) & 0xFFFF);
    temp++;
   }
  }

  if(!(bios = (uint8 *)calloc(1, 0x4000)))
  {
   CPUCleanUp();
   return 0;
  }

  if(!(internalRAM = (uint8 *)calloc(1, 0x8000)))
  {
   CPUCleanUp();
   return 0;
  }

  if(!(paletteRAM = (uint8 *)calloc(1, 0x400)))
  {
   CPUCleanUp();
   return 0;
  }

  if(!(vram = (uint8 *)calloc(1, 0x20000)))
  {
   CPUCleanUp();
   return 0;
  }

  if(!(oam = (uint8 *)calloc(1, 0x400)))
  {
   CPUCleanUp();
   return 0;
  }

  if(!(ioMem = (uint8 *)calloc(1, 0x400)))
  {
   CPUCleanUp();
   return 0;
  }

  if(!(systemColorMap = (SysCM*)malloc(sizeof(SysCM))))
  {
   CPUCleanUp();
   return(0);
  }

  CPUUpdateRenderBuffers(true);

  MDFNGameInfo->GameSetMD5Valid = FALSE;

  MDFNGBASOUND_Init();

  {
   MDFNMP_Init(0x8000, (1 << 28) / 0x8000);

   MDFNMP_AddRAM(0x40000, 0x2 << 24, workRAM);
   MDFNMP_AddRAM(0x08000, 0x3 << 24, internalRAM);
  }

  if(!CPUInit(MDFN_GetSettingS("gba.bios")))
  {
   CPUCleanUp();
   return(0);
  }
  CPUReset();

  GBA_Flash_Init();
  eepromInit();

  if (use_mednafen_save_method)
  {
   // EEPROM might be loaded from within CPUReadBatteryFile for support for Mednafen < 0.8.2, so call before GBA_EEPROM_LoadFile(), which
   // is more specific...kinda.
   if(cpuSramEnabled || cpuFlashEnabled)
    CPUReadBatteryFile(MDFN_MakeFName(MDFNMKF_SAV, 0, "sav").c_str());

   if(cpuEEPROMEnabled)
    GBA_EEPROM_LoadFile(MDFN_MakeFName(MDFNMKF_SAV, 0, "eep").c_str());
  }

  //if(!LoadCPalette(NULL, &CustomColorMap, 32768))
  //{
  // CPUCleanUp();
  // return(0);
  //}

 return(1);
}

void doMirroring (bool b)
{
  uint32 mirroredRomSize = (((romSize)>>20) & 0x3F)<<20;
  uint32 mirroredRomAddress = romSize;
  if ((mirroredRomSize <=0x800000) && (b))
  {
    mirroredRomAddress = mirroredRomSize;
    if (mirroredRomSize==0)
        mirroredRomSize=0x100000;
    while (mirroredRomAddress<0x01000000)
    {
      memcpy ((uint16 *)(rom+mirroredRomAddress), (uint16 *)(rom), mirroredRomSize);
      mirroredRomAddress+=mirroredRomSize;
    }
  }
}

static void CPUUpdateRender(void)
{
  switch(DISPCNT & 7) {
  case 0:
    if((!fxOn && !windowOn && !(layerEnable & 0x8000)) ||
       cpuDisableSfx)
      renderLine = mode0RenderLine;
    else if(fxOn && !windowOn && !(layerEnable & 0x8000))
      renderLine = mode0RenderLineNoWindow;
    else
      renderLine = mode0RenderLineAll;
    break;
  case 1:
    if((!fxOn && !windowOn && !(layerEnable & 0x8000)) ||
       cpuDisableSfx)
      renderLine = mode1RenderLine;
    else if(fxOn && !windowOn && !(layerEnable & 0x8000))
      renderLine = mode1RenderLineNoWindow;
    else
      renderLine = mode1RenderLineAll;
    break;
  case 2:
    if((!fxOn && !windowOn && !(layerEnable & 0x8000)) ||
       cpuDisableSfx)
      renderLine = mode2RenderLine;
    else if(fxOn && !windowOn && !(layerEnable & 0x8000))
      renderLine = mode2RenderLineNoWindow;
    else
      renderLine = mode2RenderLineAll;
    break;
  case 3:
    if((!fxOn && !windowOn && !(layerEnable & 0x8000)) ||
       cpuDisableSfx)
      renderLine = mode3RenderLine;
    else if(fxOn && !windowOn && !(layerEnable & 0x8000))
      renderLine = mode3RenderLineNoWindow;
    else
      renderLine = mode3RenderLineAll;
    break;
  case 4:
    if((!fxOn && !windowOn && !(layerEnable & 0x8000)) ||
       cpuDisableSfx)
      renderLine = mode4RenderLine;
    else if(fxOn && !windowOn && !(layerEnable & 0x8000))
      renderLine = mode4RenderLineNoWindow;
    else
      renderLine = mode4RenderLineAll;
    break;
  case 5:
    if((!fxOn && !windowOn && !(layerEnable & 0x8000)) ||
       cpuDisableSfx)
      renderLine = mode5RenderLine;
    else if(fxOn && !windowOn && !(layerEnable & 0x8000))
      renderLine = mode5RenderLineNoWindow;
    else
      renderLine = mode5RenderLineAll;
  default:
    break;
  }
}

void CPUUpdateCPSR()
{
  uint32 CPSR = reg[16].I & 0x40;
  if(N_FLAG)
    CPSR |= 0x80000000;
  if(Z_FLAG)
    CPSR |= 0x40000000;
  if(C_FLAG)
    CPSR |= 0x20000000;
  if(V_FLAG)
    CPSR |= 0x10000000;
  if(!armState)
    CPSR |= 0x00000020;
  if(!armIrqEnable)
    CPSR |= 0x80;
  CPSR |= (armMode & 0x1F);
  reg[16].I = CPSR;
}

void CPUUpdateFlags(bool breakLoop)
{
  uint32 CPSR = reg[16].I;

  N_FLAG = (CPSR & 0x80000000) ? true: false;
  Z_FLAG = (CPSR & 0x40000000) ? true: false;
  C_FLAG = (CPSR & 0x20000000) ? true: false;
  V_FLAG = (CPSR & 0x10000000) ? true: false;
  armState = (CPSR & 0x20) ? false : true;
  armIrqEnable = (CPSR & 0x80) ? false : true;
  if(breakLoop) {
      if (armIrqEnable && (IF & IE) && (IME & 1))
        cpuNextEvent = cpuTotalTicks;
  }
}

void CPUUpdateFlags()
{
  CPUUpdateFlags(true);
}

#ifdef MSB_FIRST
static void CPUSwap(volatile uint32 *a, volatile uint32 *b)
{
  volatile uint32 c = *b;
  *b = *a;
  *a = c;
}
#else
static void CPUSwap(uint32 *a, uint32 *b)
{
  uint32 c = *b;
  *b = *a;
  *a = c;
}
#endif

void CPUSwitchMode(int mode, bool saveState, bool breakLoop)
{
  //  if(armMode == mode)
  //    return;

  CPUUpdateCPSR();

  switch(armMode) {
  case 0x10:
  case 0x1F:
    reg[R13_USR].I = reg[13].I;
    reg[R14_USR].I = reg[14].I;
    reg[17].I = reg[16].I;
    break;
  case 0x11:
    CPUSwap(&reg[R8_FIQ].I, &reg[8].I);
    CPUSwap(&reg[R9_FIQ].I, &reg[9].I);
    CPUSwap(&reg[R10_FIQ].I, &reg[10].I);
    CPUSwap(&reg[R11_FIQ].I, &reg[11].I);
    CPUSwap(&reg[R12_FIQ].I, &reg[12].I);
    reg[R13_FIQ].I = reg[13].I;
    reg[R14_FIQ].I = reg[14].I;
    reg[SPSR_FIQ].I = reg[17].I;
    break;
  case 0x12:
    reg[R13_IRQ].I  = reg[13].I;
    reg[R14_IRQ].I  = reg[14].I;
    reg[SPSR_IRQ].I =  reg[17].I;
    break;
  case 0x13:
    reg[R13_SVC].I  = reg[13].I;
    reg[R14_SVC].I  = reg[14].I;
    reg[SPSR_SVC].I =  reg[17].I;
    break;
  case 0x17:
    reg[R13_ABT].I  = reg[13].I;
    reg[R14_ABT].I  = reg[14].I;
    reg[SPSR_ABT].I =  reg[17].I;
    break;
  case 0x1b:
    reg[R13_UND].I  = reg[13].I;
    reg[R14_UND].I  = reg[14].I;
    reg[SPSR_UND].I =  reg[17].I;
    break;
  }

  uint32 CPSR = reg[16].I;
  uint32 SPSR = reg[17].I;

  switch(mode) {
  case 0x10:
  case 0x1F:
    reg[13].I = reg[R13_USR].I;
    reg[14].I = reg[R14_USR].I;
    reg[16].I = SPSR;
    break;
  case 0x11:
    CPUSwap(&reg[8].I, &reg[R8_FIQ].I);
    CPUSwap(&reg[9].I, &reg[R9_FIQ].I);
    CPUSwap(&reg[10].I, &reg[R10_FIQ].I);
    CPUSwap(&reg[11].I, &reg[R11_FIQ].I);
    CPUSwap(&reg[12].I, &reg[R12_FIQ].I);
    reg[13].I = reg[R13_FIQ].I;
    reg[14].I = reg[R14_FIQ].I;
    if(saveState)
      reg[17].I = CPSR;
    else
      reg[17].I = reg[SPSR_FIQ].I;
    break;
  case 0x12:
    reg[13].I = reg[R13_IRQ].I;
    reg[14].I = reg[R14_IRQ].I;
    reg[16].I = SPSR;
    if(saveState)
      reg[17].I = CPSR;
    else
      reg[17].I = reg[SPSR_IRQ].I;
    break;
  case 0x13:
    reg[13].I = reg[R13_SVC].I;
    reg[14].I = reg[R14_SVC].I;
    reg[16].I = SPSR;
    if(saveState)
      reg[17].I = CPSR;
    else
      reg[17].I = reg[SPSR_SVC].I;
    break;
  case 0x17:
    reg[13].I = reg[R13_ABT].I;
    reg[14].I = reg[R14_ABT].I;
    reg[16].I = SPSR;
    if(saveState)
      reg[17].I = CPSR;
    else
      reg[17].I = reg[SPSR_ABT].I;
    break;
  case 0x1b:
    reg[13].I = reg[R13_UND].I;
    reg[14].I = reg[R14_UND].I;
    reg[16].I = SPSR;
    if(saveState)
      reg[17].I = CPSR;
    else
      reg[17].I = reg[SPSR_UND].I;
    break;
  default:
    //systemMessage(MSG_UNSUPPORTED_ARM_MODE, N_("Unsupported ARM mode %02x"), mode);
    break;
  }
  armMode = mode;
  CPUUpdateFlags(breakLoop);
  CPUUpdateCPSR();
}

void CPUSwitchMode(int mode, bool saveState)
{
  CPUSwitchMode(mode, saveState, true);
}

void CPUUndefinedException()
{
  uint32 PC = reg[15].I;
  bool savedArmState = armState;
  CPUSwitchMode(0x1b, true, false);
  reg[14].I = PC - (savedArmState ? 4 : 2);
  reg[15].I = 0x04;
  armState = true;
  armIrqEnable = false;
  armNextPC = 0x04;
  ARM_PREFETCH;
  reg[15].I += 4;
}

void CPUSoftwareInterrupt()
{
  uint32 PC = reg[15].I;
  bool savedArmState = armState;
  CPUSwitchMode(0x13, true, false);
  reg[14].I = PC - (savedArmState ? 4 : 2);
  reg[15].I = 0x08;
  armState = true;
  armIrqEnable = false;
  armNextPC = 0x08;
  ARM_PREFETCH;
  reg[15].I += 4;
}

void CPUSoftwareInterrupt(int comment)
{
  static bool disableMessage = true;
  if(armState) comment >>= 16;
  if(comment == 0xfa) {
    return;
  }
  if(useBios) {
    CPUSoftwareInterrupt();
    return;
  }
  // This would be correct, but it causes problems if uncommented
  //  else {
  //    biosProtected = 0xe3a02004;
  //  }

  switch(comment) {
  case 0x00:
    BIOS_SoftReset();
    ARM_PREFETCH;
    break;
  case 0x01:
    BIOS_RegisterRamReset();
    break;
  case 0x02:
    holdState = true;
    holdType = -1;
    cpuNextEvent = cpuTotalTicks;
    break;
  case 0x03:
    holdState = true;
    holdType = -1;
    stopState = true;
    cpuNextEvent = cpuTotalTicks;
    break;
  case 0x04:
    CPUSoftwareInterrupt();
    break;
  case 0x05:
    CPUSoftwareInterrupt();
    break;
  case 0x06:
    CPUSoftwareInterrupt();
    break;
  case 0x07:
    CPUSoftwareInterrupt();
    break;
  case 0x08:
    BIOS_Sqrt();
    break;
  case 0x09:
    BIOS_ArcTan();
    break;
  case 0x0A:
    BIOS_ArcTan2();
    break;
  case 0x0B:
    {
      int len = (reg[2].I & 0x1FFFFF) >>1;
      if (!(((reg[0].I & 0xe000000) == 0) ||
         ((reg[0].I + len) & 0xe000000) == 0))
      {
        if ((reg[2].I >> 24) & 1)
        {
          if ((reg[2].I >> 26) & 1)
          SWITicks = (7 + memoryWait32[(reg[1].I>>24) & 0xF]) * (len>>1);
          else
          SWITicks = (8 + memoryWait[(reg[1].I>>24) & 0xF]) * (len);
        }
        else
        {
          if ((reg[2].I >> 26) & 1)
          SWITicks = (10 + memoryWait32[(reg[0].I>>24) & 0xF] +
              memoryWait32[(reg[1].I>>24) & 0xF]) * (len>>1);
          else
          SWITicks = (11 + memoryWait[(reg[0].I>>24) & 0xF] +
              memoryWait[(reg[1].I>>24) & 0xF]) * len;
        }
      }
    }
    BIOS_CpuSet();
    break;
  case 0x0C:
    {
      int len = (reg[2].I & 0x1FFFFF) >>5;
      if (!(((reg[0].I & 0xe000000) == 0) ||
         ((reg[0].I + len) & 0xe000000) == 0))
      {
        if ((reg[2].I >> 24) & 1)
          SWITicks = (6 + memoryWait32[(reg[1].I>>24) & 0xF] +
              7 * (memoryWaitSeq32[(reg[1].I>>24) & 0xF] + 1)) * len;
        else
          SWITicks = (9 + memoryWait32[(reg[0].I>>24) & 0xF] +
              memoryWait32[(reg[1].I>>24) & 0xF] +
              7 * (memoryWaitSeq32[(reg[0].I>>24) & 0xF] +
              memoryWaitSeq32[(reg[1].I>>24) & 0xF] + 2)) * len;
      }
    }
    BIOS_CpuFastSet();
    break;
  case 0x0E:
    BIOS_BgAffineSet();
    break;
  case 0x0F:
    BIOS_ObjAffineSet();
    break;
  case 0x10:
    {
      int len = CPUReadHalfWord(reg[2].I);
      if (!(((reg[0].I & 0xe000000) == 0) ||
         ((reg[0].I + len) & 0xe000000) == 0))
        SWITicks = (32 + memoryWait[(reg[0].I>>24) & 0xF]) * len;
    }
    BIOS_BitUnPack();
    break;
  case 0x11:
    {
      uint32 len = CPUReadMemory(reg[0].I) >> 8;
      if(!(((reg[0].I & 0xe000000) == 0) ||
          ((reg[0].I + (len & 0x1fffff)) & 0xe000000) == 0))
        SWITicks = (9 + memoryWait[(reg[1].I>>24) & 0xF]) * len;
    }
    BIOS_LZ77UnCompWram();
    break;
  case 0x12:
    {
      uint32 len = CPUReadMemory(reg[0].I) >> 8;
      if(!(((reg[0].I & 0xe000000) == 0) ||
          ((reg[0].I + (len & 0x1fffff)) & 0xe000000) == 0))
        SWITicks = (19 + memoryWait[(reg[1].I>>24) & 0xF]) * len;
    }
    BIOS_LZ77UnCompVram();
    break;
  case 0x13:
    {
      uint32 len = CPUReadMemory(reg[0].I) >> 8;
      if(!(((reg[0].I & 0xe000000) == 0) ||
          ((reg[0].I + (len & 0x1fffff)) & 0xe000000) == 0))
        SWITicks = (29 + (memoryWait[(reg[0].I>>24) & 0xF]<<1)) * len;
    }
    BIOS_HuffUnComp();
    break;
  case 0x14:
    {
      uint32 len = CPUReadMemory(reg[0].I) >> 8;
      if(!(((reg[0].I & 0xe000000) == 0) ||
          ((reg[0].I + (len & 0x1fffff)) & 0xe000000) == 0))
        SWITicks = (11 + memoryWait[(reg[0].I>>24) & 0xF] +
          memoryWait[(reg[1].I>>24) & 0xF]) * len;
    }
    BIOS_RLUnCompWram();
    break;
  case 0x15:
    {
      uint32 len = CPUReadMemory(reg[0].I) >> 9;
      if(!(((reg[0].I & 0xe000000) == 0) ||
          ((reg[0].I + (len & 0x1fffff)) & 0xe000000) == 0))
        SWITicks = (34 + (memoryWait[(reg[0].I>>24) & 0xF] << 1) +
          memoryWait[(reg[1].I>>24) & 0xF]) * len;
    }
    BIOS_RLUnCompVram();
    break;
  case 0x16:
    {
      uint32 len = CPUReadMemory(reg[0].I) >> 8;
      if(!(((reg[0].I & 0xe000000) == 0) ||
          ((reg[0].I + (len & 0x1fffff)) & 0xe000000) == 0))
        SWITicks = (13 + memoryWait[(reg[0].I>>24) & 0xF] +
          memoryWait[(reg[1].I>>24) & 0xF]) * len;
    }
    BIOS_Diff8bitUnFilterWram();
    break;
  case 0x17:
    {
      uint32 len = CPUReadMemory(reg[0].I) >> 9;
      if(!(((reg[0].I & 0xe000000) == 0) ||
          ((reg[0].I + (len & 0x1fffff)) & 0xe000000) == 0))
        SWITicks = (39 + (memoryWait[(reg[0].I>>24) & 0xF]<<1) +
          memoryWait[(reg[1].I>>24) & 0xF]) * len;
    }
    BIOS_Diff8bitUnFilterVram();
    break;
  case 0x18:
    {
      uint32 len = CPUReadMemory(reg[0].I) >> 9;
      if(!(((reg[0].I & 0xe000000) == 0) ||
          ((reg[0].I + (len & 0x1fffff)) & 0xe000000) == 0))
        SWITicks = (13 + memoryWait[(reg[0].I>>24) & 0xF] +
          memoryWait[(reg[1].I>>24) & 0xF]) * len;
    }
    BIOS_Diff16bitUnFilter();
    break;
  case 0x19:
    //if(reg[0].I)
    //  systemSoundPause();
    //else
    //  systemSoundResume();
    break;
  case 0x1F:
    BIOS_MidiKey2Freq();
    break;
  case 0x2A:
    BIOS_SndDriverJmpTableCopy();
    // let it go, because we don't really emulate this function
  default:
    if(!disableMessage) {
      MDFN_PrintError(_("Unsupported BIOS function %02x called from %08x. A BIOS file is needed in order to get correct behaviour."),
                    comment,
                    armMode ? armNextPC - 4: armNextPC - 2);
      disableMessage = true;
    }
    break;
  }
}

static void CPUCompareVCOUNT()
{
  if(VCOUNT == (DISPSTAT >> 8)) {
    DISPSTAT |= 4;
    UPDATE_REG(0x04, DISPSTAT);

    if(DISPSTAT & 0x20) {
      IF |= 4;
      UPDATE_REG(0x202, IF);
    }
  } else {
    DISPSTAT &= 0xFFFB;
    UPDATE_REG(0x4, DISPSTAT);
  }
  if (layerEnableDelay>0)
  {
      layerEnableDelay--;
      if (layerEnableDelay==1)
          layerEnable = layerSettings & DISPCNT;
  }

}

#define doDMA(s, d, _si, _di, _c, _transfer32)	\
{	\
  uint32 si = _si;	\
  uint32 di = _di;	\
  uint32 c = _c;	\
  int sm = s >> 24;	\
  int dm = d >> 24;	\
  int sw = 0;	\
  int dw = 0;	\
  int sc = c;	\
  cpuDmaCount = c;	\
  if (sm>15)	\
      sm=15;	\
  if (dm>15)	\
      dm=15;	\
  if(_transfer32) {	\
    s &= 0xFFFFFFFC;	\
    if(s < 0x02000000 && (reg[15].I >> 24)) {	\
      while(c != 0) {	\
        CPUWriteMemory(d, 0);	\
        d += di;	\
        c--;	\
      }	\
    } else {	\
      while(c != 0) {	\
        cpuDmaLast = CPUReadMemory(s);	\
        CPUWriteMemory(d, cpuDmaLast);	\
        d += di;	\
        s += si;	\
        c--;	\
      }	\
    }	\
  } else {	\
    s &= 0xFFFFFFFE;	\
    si = (int)si >> 1;	\
    di = (int)di >> 1;	\
    if(s < 0x02000000 && (reg[15].I >> 24)) {	\
      while(c != 0) {	\
        CPUWriteHalfWord(d, 0);	\
        d += di;	\
        c--;	\
      }	\
    } else {	\
      while(c != 0) {	\
        cpuDmaLast = CPUReadHalfWord(s);	\
        CPUWriteHalfWord(d, cpuDmaLast);	\
        cpuDmaLast |= (cpuDmaLast<<16);	\
        d += di;	\
        s += si;	\
        c--;	\
      }	\
    }	\
  }	\
  cpuDmaCount = 0;	\
  int totalTicks = 0;	\
  if(_transfer32) {	\
      sw =1+memoryWaitSeq32[sm & 15];	\
      dw =1+memoryWaitSeq32[dm & 15];	\
      totalTicks = (sw+dw)*(sc-1) + 6 + memoryWait32[sm & 15] +	\
          memoryWaitSeq32[dm & 15];	\
  }	\
  else	\
  {	\
     sw = 1+memoryWaitSeq[sm & 15];	\
     dw = 1+memoryWaitSeq[dm & 15];	\
      totalTicks = (sw+dw)*(sc-1) + 6 + memoryWait[sm & 15] +	\
          memoryWaitSeq[dm & 15];	\
  }	\
  cpuDmaTicksToUpdate += totalTicks;	\
}

void CPUCheckDMA(int reason, int dmamask)
{
  // DMA 0
  if((DMCNT_H[0] & 0x8000) && (dmamask & 1)) {
    if(((DMCNT_H[0] >> 12) & 3) == reason) {
      uint32 sourceIncrement = 4;
      uint32 destIncrement = 4;
      switch((DMCNT_H[0] >> 7) & 3) {
      case 0:
        break;
      case 1:
        sourceIncrement = (uint32)-4;
        break;
      case 2:
        sourceIncrement = 0;
        break;
      }
      switch((DMCNT_H[0] >> 5) & 3) {
      case 0:
        break;
      case 1:
        destIncrement = (uint32)-4;
        break;
      case 2:
        destIncrement = 0;
        break;
      }
      doDMA(dmaSource[0], dmaDest[0], sourceIncrement, destIncrement,
            DMCNT_L[0] ? DMCNT_L[0] : 0x4000,
            DMCNT_H[0] & 0x0400);
      cpuDmaHack = true;

      if(DMCNT_H[0] & 0x4000) {
        IF |= 0x0100;
        UPDATE_REG(0x202, IF);
        cpuNextEvent = cpuTotalTicks;
      }

      if(((DMCNT_H[0] >> 5) & 3) == 3) {
        dmaDest[0] = DMDAD_L[0] | (DMDAD_H[0] << 16);
      }

      if(!(DMCNT_H[0] & 0x0200) || (reason == 0)) {
        DMCNT_H[0] &= 0x7FFF;
        UPDATE_REG(0xBA, DMCNT_H[0]);
      }
    }
  }

  // DMA 1
  if((DMCNT_H[1] & 0x8000) && (dmamask & 2)) {
    if(((DMCNT_H[1] >> 12) & 3) == reason) {
      uint32 sourceIncrement = 4;
      uint32 destIncrement = 4;
      switch((DMCNT_H[1] >> 7) & 3) {
      case 0:
        break;
      case 1:
        sourceIncrement = (uint32)-4;
        break;
      case 2:
        sourceIncrement = 0;
        break;
      }
      switch((DMCNT_H[1] >> 5) & 3) {
      case 0:
        break;
      case 1:
        destIncrement = (uint32)-4;
        break;
      case 2:
        destIncrement = 0;
        break;
      }
      if(reason == 3) {
        doDMA(dmaSource[1], dmaDest[1], sourceIncrement, 0, 4,
              0x0400);
      } else {
        doDMA(dmaSource[1], dmaDest[1], sourceIncrement, destIncrement,
              DMCNT_L[1] ? DMCNT_L[1] : 0x4000,
              DMCNT_H[1] & 0x0400);
      }
      cpuDmaHack = true;

      if(DMCNT_H[1] & 0x4000) {
        IF |= 0x0200;
        UPDATE_REG(0x202, IF);
        cpuNextEvent = cpuTotalTicks;
      }

      if(((DMCNT_H[1] >> 5) & 3) == 3) {
        dmaDest[1] = DMDAD_L[1] | (DMDAD_H[1] << 16);
      }

      if(!(DMCNT_H[1] & 0x0200) || (reason == 0)) {
        DMCNT_H[1] &= 0x7FFF;
        UPDATE_REG(0xC6, DMCNT_H[1]);
      }
    }
  }

  // DMA 2
  if((DMCNT_H[2] & 0x8000) && (dmamask & 4)) {
    if(((DMCNT_H[2] >> 12) & 3) == reason) {
      uint32 sourceIncrement = 4;
      uint32 destIncrement = 4;
      switch((DMCNT_H[2] >> 7) & 3) {
      case 0:
        break;
      case 1:
        sourceIncrement = (uint32)-4;
        break;
      case 2:
        sourceIncrement = 0;
        break;
      }
      switch((DMCNT_H[2] >> 5) & 3) {
      case 0:
        break;
      case 1:
        destIncrement = (uint32)-4;
        break;
      case 2:
        destIncrement = 0;
        break;
      }
      if(reason == 3) {
        doDMA(dmaSource[2], dmaDest[2], sourceIncrement, 0, 4,
              0x0400);
      } else {
        doDMA(dmaSource[2], dmaDest[2], sourceIncrement, destIncrement,
              DMCNT_L[2] ? DMCNT_L[2] : 0x4000,
              DMCNT_H[2] & 0x0400);
      }
      cpuDmaHack = true;

      if(DMCNT_H[2] & 0x4000) {
        IF |= 0x0400;
        UPDATE_REG(0x202, IF);
        cpuNextEvent = cpuTotalTicks;
      }

      if(((DMCNT_H[2] >> 5) & 3) == 3) {
        dmaDest[2] = DMDAD_L[2] | (DMDAD_H[2] << 16);
      }

      if(!(DMCNT_H[2] & 0x0200) || (reason == 0)) {
        DMCNT_H[2] &= 0x7FFF;
        UPDATE_REG(0xD2, DMCNT_H[2]);
      }
    }
  }

  // DMA 3
  if((DMCNT_H[3] & 0x8000) && (dmamask & 8)) {
    if(((DMCNT_H[3] >> 12) & 3) == reason) {
      uint32 sourceIncrement = 4;
      uint32 destIncrement = 4;
      switch((DMCNT_H[3] >> 7) & 3) {
      case 0:
        break;
      case 1:
        sourceIncrement = (uint32)-4;
        break;
      case 2:
        sourceIncrement = 0;
        break;
      }
      switch((DMCNT_H[3] >> 5) & 3) {
      case 0:
        break;
      case 1:
        destIncrement = (uint32)-4;
        break;
      case 2:
        destIncrement = 0;
        break;
      }
      doDMA(dmaSource[3], dmaDest[3], sourceIncrement, destIncrement,
            DMCNT_L[3] ? DMCNT_L[3] : 0x10000,
            DMCNT_H[3] & 0x0400);
      if(DMCNT_H[3] & 0x4000) {
        IF |= 0x0800;
        UPDATE_REG(0x202, IF);
        cpuNextEvent = cpuTotalTicks;
      }

      if(((DMCNT_H[3] >> 5) & 3) == 3) {
        dmaDest[3] = DMDAD_L[3] | (DMDAD_H[3] << 16);
      }

      if(!(DMCNT_H[3] & 0x0200) || (reason == 0)) {
        DMCNT_H[3] &= 0x7FFF;
        UPDATE_REG(0xDE, DMCNT_H[3]);
      }
    }
  }
}

void CPUUpdateRegister(uint32 address, uint16 value)
{
  switch(address)
  {
  case 0x00:
    {
      if ((value & 7) >5)
          DISPCNT = (value &7);
      bool change = ((DISPCNT ^ value) & 0x80) ? true : false;
      bool changeBG = ((DISPCNT ^ value) & 0x0F00) ? true : false;
      uint16 changeBGon = (((~DISPCNT) & value) & 0x0F00);
      DISPCNT = (value & 0xFFF7);
      UPDATE_REG(0x00, DISPCNT);

      if (changeBGon)
      {
         layerEnableDelay=4;
         layerEnable = layerSettings & value & (~changeBGon);
      }
       else
         layerEnable = layerSettings & value;
      //      CPUUpdateTicks();

      windowOn = (layerEnable & 0x6000) ? true : false;
      if(change && !((value & 0x80))) {
        if(!(DISPSTAT & 1)) {
          lcdTicks = 1008;
          //      VCOUNT = 0;
          //      UPDATE_REG(0x06, VCOUNT);
          DISPSTAT &= 0xFFFC;
          UPDATE_REG(0x04, DISPSTAT);
          CPUCompareVCOUNT();
        }
        //        (*renderLine)();
      }
      CPUUpdateRender();
      // we only care about changes in BG0-BG3
      if(changeBG)
        CPUUpdateRenderBuffers(false);
    }
    break;
  case 0x04:
    DISPSTAT = (value & 0xFF38) | (DISPSTAT & 7);
    UPDATE_REG(0x04, DISPSTAT);
    break;
  case 0x06:
    // not writable
    break;
  case 0x08:
    BG0CNT = (value & 0xDFCF);
    UPDATE_REG(0x08, BG0CNT);
    break;
  case 0x0A:
    BG1CNT = (value & 0xDFCF);
    UPDATE_REG(0x0A, BG1CNT);
    break;
  case 0x0C:
    BG2CNT = (value & 0xFFCF);
    UPDATE_REG(0x0C, BG2CNT);
    break;
  case 0x0E:
    BG3CNT = (value & 0xFFCF);
    UPDATE_REG(0x0E, BG3CNT);
    break;
  case 0x10:
    BGHOFS[0] = value & 511;
    UPDATE_REG(0x10, BGHOFS[0]);
    break;
  case 0x12:
    BGVOFS[0] = value & 511;
    UPDATE_REG(0x12, BGVOFS[0]);
    break;
  case 0x14:
    BGHOFS[1] = value & 511;
    UPDATE_REG(0x14, BGHOFS[1]);
    break;
  case 0x16:
    BGVOFS[1] = value & 511;
    UPDATE_REG(0x16, BGVOFS[1]);
    break;
  case 0x18:
    BGHOFS[2] = value & 511;
    UPDATE_REG(0x18, BGHOFS[2]);
    break;
  case 0x1A:
    BGVOFS[2] = value & 511;
    UPDATE_REG(0x1A, BGVOFS[2]);
    break;
  case 0x1C:
    BGHOFS[3] = value & 511;
    UPDATE_REG(0x1C, BGHOFS[3]);
    break;
  case 0x1E:
    BGVOFS[3] = value & 511;
    UPDATE_REG(0x1E, BGVOFS[3]);
    break;
  case 0x20:
    BG2PA = value;
    UPDATE_REG(0x20, BG2PA);
    break;
  case 0x22:
    BG2PB = value;
    UPDATE_REG(0x22, BG2PB);
    break;
  case 0x24:
    BG2PC = value;
    UPDATE_REG(0x24, BG2PC);
    break;
  case 0x26:
    BG2PD = value;
    UPDATE_REG(0x26, BG2PD);
    break;
  case 0x28:
    BG2X_L = value;
    UPDATE_REG(0x28, BG2X_L);
    gfxBG2Changed |= 1;
    break;
  case 0x2A:
    BG2X_H = (value & 0xFFF);
    UPDATE_REG(0x2A, BG2X_H);
    gfxBG2Changed |= 1;
    break;
  case 0x2C:
    BG2Y_L = value;
    UPDATE_REG(0x2C, BG2Y_L);
    gfxBG2Changed |= 2;
    break;
  case 0x2E:
    BG2Y_H = value & 0xFFF;
    UPDATE_REG(0x2E, BG2Y_H);
    gfxBG2Changed |= 2;
    break;
  case 0x30:
    BG3PA = value;
    UPDATE_REG(0x30, BG3PA);
    break;
  case 0x32:
    BG3PB = value;
    UPDATE_REG(0x32, BG3PB);
    break;
  case 0x34:
    BG3PC = value;
    UPDATE_REG(0x34, BG3PC);
    break;
  case 0x36:
    BG3PD = value;
    UPDATE_REG(0x36, BG3PD);
    break;
  case 0x38:
    BG3X_L = value;
    UPDATE_REG(0x38, BG3X_L);
    gfxBG3Changed |= 1;
    break;
  case 0x3A:
    BG3X_H = value & 0xFFF;
    UPDATE_REG(0x3A, BG3X_H);
    gfxBG3Changed |= 1;
    break;
  case 0x3C:
    BG3Y_L = value;
    UPDATE_REG(0x3C, BG3Y_L);
    gfxBG3Changed |= 2;
    break;
  case 0x3E:
    BG3Y_H = value & 0xFFF;
    UPDATE_REG(0x3E, BG3Y_H);
    gfxBG3Changed |= 2;
    break;
  case 0x40:
    WIN0H = value;
    UPDATE_REG(0x40, WIN0H);
    CPUUpdateWindow0();
    break;
  case 0x42:
    WIN1H = value;
    UPDATE_REG(0x42, WIN1H);
    CPUUpdateWindow1();
    break;
  case 0x44:
    WIN0V = value;
    UPDATE_REG(0x44, WIN0V);
    break;
  case 0x46:
    WIN1V = value;
    UPDATE_REG(0x46, WIN1V);
    break;
  case 0x48:
    WININ = value & 0x3F3F;
    UPDATE_REG(0x48, WININ);
    break;
  case 0x4A:
    WINOUT = value & 0x3F3F;
    UPDATE_REG(0x4A, WINOUT);
    break;
  case 0x4C:
    MOSAIC = value;
    UPDATE_REG(0x4C, MOSAIC);
    break;
  case 0x50:
    BLDMOD = value & 0x3FFF;
    UPDATE_REG(0x50, BLDMOD);
    fxOn = ((BLDMOD>>6)&3) != 0;
    CPUUpdateRender();
    break;
  case 0x52:
    COLEV = value & 0x1F1F;
    UPDATE_REG(0x52, COLEV);
    break;
  case 0x54:
    COLY = value & 0x1F;
    UPDATE_REG(0x54, COLY);
    break;
  case 0x60:
  case 0x62:
  case 0x64:
  case 0x68:
  case 0x6c:
  case 0x70:
  case 0x72:
  case 0x74:
  case 0x78:
  case 0x7c:
  case 0x80:
  case 0x84:
    soundEvent(address&0xFF, (uint8)(value & 0xFF));
    soundEvent((address&0xFF)+1, (uint8)(value>>8));
    break;
  case 0x82:
  case 0x88:
  case 0xa0:
  case 0xa2:
  case 0xa4:
  case 0xa6:
  case 0x90:
  case 0x92:
  case 0x94:
  case 0x96:
  case 0x98:
  case 0x9a:
  case 0x9c:
  case 0x9e:
    soundEvent(address&0xFF, value);
    break;
  case 0xB0:
    DMSAD_L[0] = value;
    UPDATE_REG(0xB0, DMSAD_L[0]);
    break;
  case 0xB2:
    DMSAD_H[0] = value & 0x07FF;
    UPDATE_REG(0xB2, DMSAD_H[0]);
    break;
  case 0xB4:
    DMDAD_L[0] = value;
    UPDATE_REG(0xB4, DMDAD_L[0]);
    break;
  case 0xB6:
    DMDAD_H[0] = value & 0x07FF;
    UPDATE_REG(0xB6, DMDAD_H[0]);
    break;
  case 0xB8:
    DMCNT_L[0] = value & 0x3FFF;
    UPDATE_REG(0xB8, 0);
    break;
  case 0xBA:
    {
      bool start = ((DMCNT_H[0] ^ value) & 0x8000) ? true : false;
      value &= 0xF7E0;

      DMCNT_H[0] = value;
      UPDATE_REG(0xBA, DMCNT_H[0]);

      if(start && (value & 0x8000)) {
        dmaSource[0] = DMSAD_L[0] | (DMSAD_H[0] << 16);
        dmaDest[0] = DMDAD_L[0] | (DMDAD_H[0] << 16);
        CPUCheckDMA(0, 1);
      }
    }
    break;
  case 0xBC:
    DMSAD_L[1] = value;
    UPDATE_REG(0xBC, DMSAD_L[1]);
    break;
  case 0xBE:
    DMSAD_H[1] = value & 0x0FFF;
    UPDATE_REG(0xBE, DMSAD_H[1]);
    break;
  case 0xC0:
    DMDAD_L[1] = value;
    UPDATE_REG(0xC0, DMDAD_L[1]);
    break;
  case 0xC2:
    DMDAD_H[1] = value & 0x07FF;
    UPDATE_REG(0xC2, DMDAD_H[1]);
    break;
  case 0xC4:
    DMCNT_L[1] = value & 0x3FFF;
    UPDATE_REG(0xC4, 0);
    break;
  case 0xC6:
    {
      bool start = ((DMCNT_H[1] ^ value) & 0x8000) ? true : false;
      value &= 0xF7E0;

      DMCNT_H[1] = value;
      UPDATE_REG(0xC6, DMCNT_H[1]);

      if(start && (value & 0x8000)) {
        dmaSource[1] = DMSAD_L[1] | (DMSAD_H[1] << 16);
        dmaDest[1] = DMDAD_L[1] | (DMDAD_H[1] << 16);
        CPUCheckDMA(0, 2);
      }
    }
    break;
  case 0xC8:
    DMSAD_L[2] = value;
    UPDATE_REG(0xC8, DMSAD_L[2]);
    break;
  case 0xCA:
    DMSAD_H[2] = value & 0x0FFF;
    UPDATE_REG(0xCA, DMSAD_H[2]);
    break;
  case 0xCC:
    DMDAD_L[2] = value;
    UPDATE_REG(0xCC, DMDAD_L[2]);
    break;
  case 0xCE:
    DMDAD_H[2] = value & 0x07FF;
    UPDATE_REG(0xCE, DMDAD_H[2]);
    break;
  case 0xD0:
    DMCNT_L[2] = value & 0x3FFF;
    UPDATE_REG(0xD0, 0);
    break;
  case 0xD2:
    {
      bool start = ((DMCNT_H[2] ^ value) & 0x8000) ? true : false;

      value &= 0xF7E0;

      DMCNT_H[2] = value;
      UPDATE_REG(0xD2, DMCNT_H[2]);

      if(start && (value & 0x8000)) {
        dmaSource[2] = DMSAD_L[2] | (DMSAD_H[2] << 16);
        dmaDest[2] = DMDAD_L[2] | (DMDAD_H[2] << 16);

        CPUCheckDMA(0, 4);
      }
    }
    break;
  case 0xD4:
    DMSAD_L[3] = value;
    UPDATE_REG(0xD4, DMSAD_L[3]);
    break;
  case 0xD6:
    DMSAD_H[3] = value & 0x0FFF;
    UPDATE_REG(0xD6, DMSAD_H[3]);
    break;
  case 0xD8:
    DMDAD_L[3] = value;
    UPDATE_REG(0xD8, DMDAD_L[3]);
    break;
  case 0xDA:
    DMDAD_H[3] = value & 0x0FFF;
    UPDATE_REG(0xDA, DMDAD_H[3]);
    break;
  case 0xDC:
    DMCNT_L[3] = value;
    UPDATE_REG(0xDC, 0);
    break;
  case 0xDE:
    {
      bool start = ((DMCNT_H[3] ^ value) & 0x8000) ? true : false;

      value &= 0xFFE0;

      DMCNT_H[3] = value;
      UPDATE_REG(0xDE, DMCNT_H[3]);

      if(start && (value & 0x8000)) {
        dmaSource[3] = DMSAD_L[3] | (DMSAD_H[3] << 16);
        dmaDest[3] = DMDAD_L[3] | (DMDAD_H[3] << 16);
        CPUCheckDMA(0,8);
      }
    }
    break;
 case 0x100:
    timers[0].Reload = value;
    break;
  case 0x102:
    timers[0].Value = value;
    timerOnOffDelay|=1;
    cpuNextEvent = cpuTotalTicks;
    break;
  case 0x104:
    timers[1].Reload = value;
    break;
  case 0x106:
    timers[1].Value = value;
    timerOnOffDelay|=2;
    cpuNextEvent = cpuTotalTicks;
    break;
  case 0x108:
    timers[2].Reload = value;
    break;
  case 0x10A:
    timers[2].Value = value;
    timerOnOffDelay|=4;
    cpuNextEvent = cpuTotalTicks;
    break;
  case 0x10C:
    timers[3].Reload = value;
    break;
  case 0x10E:
    timers[3].Value = value;
    timerOnOffDelay|=8;
    cpuNextEvent = cpuTotalTicks;
    break;
  case 0x128:
    if(value & 0x80) {
      value &= 0xff7f;
      if(value & 1 && (value & 0x4000)) {
        UPDATE_REG(0x12a, 0xFF);
        IF |= 0x80;
        UPDATE_REG(0x202, IF);
        value &= 0x7f7f;
      }
    }
    UPDATE_REG(0x128, value);
    break;
  case 0x130:
    P1 |= (value & 0x3FF);
    UPDATE_REG(0x130, P1);
    break;
  case 0x132:
    UPDATE_REG(0x132, value & 0xC3FF);
    break;
  case 0x200:
    IE = value & 0x3FFF;
    UPDATE_REG(0x200, IE);
    if ((IME & 1) && (IF & IE) && armIrqEnable)
      cpuNextEvent = cpuTotalTicks;
    break;
  case 0x202:
    IF ^= (value & IF);
    UPDATE_REG(0x202, IF);
    break;
  case 0x204:
    {
      memoryWait[0x0e] = memoryWaitSeq[0x0e] = gamepakRamWaitState[value & 3];

      memoryWait[0x08] = memoryWait[0x09] = gamepakWaitState[(value >> 2) & 3];
      memoryWaitSeq[0x08] = memoryWaitSeq[0x09] =
        gamepakWaitState0[(value >> 4) & 1];

      memoryWait[0x0a] = memoryWait[0x0b] = gamepakWaitState[(value >> 5) & 3];
      memoryWaitSeq[0x0a] = memoryWaitSeq[0x0b] =
        gamepakWaitState1[(value >> 7) & 1];

      memoryWait[0x0c] = memoryWait[0x0d] = gamepakWaitState[(value >> 8) & 3];
      memoryWaitSeq[0x0c] = memoryWaitSeq[0x0d] =
        gamepakWaitState2[(value >> 10) & 1];

      for(int i = 8; i < 15; i++) {
        memoryWait32[i] = memoryWait[i] + memoryWaitSeq[i] + 1;
        memoryWaitSeq32[i] = memoryWaitSeq[i]*2 + 1;
      }

      if((value & 0x4000) == 0x4000) {
        busPrefetchEnable = true;
        busPrefetch = false;
        busPrefetchCount = 0;
      } else {
        busPrefetchEnable = false;
        busPrefetch = false;
        busPrefetchCount = 0;
      }
      UPDATE_REG(0x204, value & 0x7FFF);

    }
    break;
  case 0x208:
    IME = value & 1;
    UPDATE_REG(0x208, IME);
    if ((IME & 1) && (IF & IE) && armIrqEnable)
      cpuNextEvent = cpuTotalTicks;
    break;
  case 0x300:
    if(value != 0)
      value &= 0xFFFE;
    UPDATE_REG(0x300, value);
    break;
  default:
    UPDATE_REG(address&0x3FE, value);
    break;
  }
}

void applyTimer ()
{
  if (timerOnOffDelay & 1)
  {
    timers[0].ClockReload = TIMER_TICKS[timers[0].Value & 3];
    if(!timers[0].On && (timers[0].Value & 0x80)) {
      // reload the counter
      timers[0].D = timers[0].Reload;
      timers[0].Ticks = (0x10000 - timers[0].D) << timers[0].ClockReload;
      UPDATE_REG(0x100, timers[0].D);
    }
    timers[0].On = timers[0].Value & 0x80 ? true : false;
    timers[0].CNT = timers[0].Value & 0xC7;
    UPDATE_REG(0x102, timers[0].CNT);
    //    CPUUpdateTicks();
  }
  if (timerOnOffDelay & 2)
  {
    timers[1].ClockReload = TIMER_TICKS[timers[1].Value & 3];
    if(!timers[1].On && (timers[1].Value & 0x80)) {
      // reload the counter
      timers[1].D = timers[1].Reload;
      timers[1].Ticks = (0x10000 - timers[1].D) << timers[1].ClockReload;
      UPDATE_REG(0x104, timers[1].D);
    }
    timers[1].On = timers[1].Value & 0x80 ? true : false;
    timers[1].CNT = timers[1].Value & 0xC7;
    UPDATE_REG(0x106, timers[1].CNT);
  }
  if (timerOnOffDelay & 4)
  {
    timers[2].ClockReload = TIMER_TICKS[timers[2].Value & 3];
    if(!timers[2].On && (timers[2].Value & 0x80)) {
      // reload the counter
      timers[2].D = timers[2].Reload;
      timers[2].Ticks = (0x10000 - timers[2].D) << timers[2].ClockReload;
      UPDATE_REG(0x108, timers[2].D);
    }
    timers[2].On = timers[2].Value & 0x80 ? true : false;
    timers[2].CNT = timers[2].Value & 0xC7;
    UPDATE_REG(0x10A, timers[2].CNT);
  }
  if (timerOnOffDelay & 8)
  {
    timers[3].ClockReload = TIMER_TICKS[timers[3].Value & 3];
    if(!timers[3].On && (timers[3].Value & 0x80)) {
      // reload the counter
      timers[3].D = timers[3].Reload;
      timers[3].Ticks = (0x10000 - timers[3].D) << timers[3].ClockReload;
      UPDATE_REG(0x10C, timers[3].D);
    }
    timers[3].On = timers[3].Value & 0x80 ? true : false;
    timers[3].CNT = timers[3].Value & 0xC7;
    UPDATE_REG(0x10E, timers[3].CNT);
  }
  cpuNextEvent = CPUUpdateTicks();
  timerOnOffDelay = 0;
}

static void FLASH_SRAM_Write(uint32 A, uint32 V)
{
// printf("%08x %08x\n", A, V);

 if(cpuFlashEnabled && cpuSramEnabled)
 {
  if((A & 0xFFFF) == 0x5555 && (V & 0xFF) == 0xAA)
   cpuSramEnabled = FALSE;
  else if((A & 0xFFFF) != 0x2AAA)
   cpuFlashEnabled = FALSE;

  if(!cpuFlashEnabled || !cpuSramEnabled)
   printf("%s emulation disabled by write to:  %08x %08x\n", cpuSramEnabled ? "FLASH" : "SRAM", A, V);
 }

 if(cpuSramEnabled)
  sramWrite(A, V);

 if(cpuFlashEnabled)
 flashWrite(A, V);
}

void CPUWriteMemory(uint32 address, uint32 value)
{
 switch(address >> 24)
 {
  case 0x02:
      WRITE32LE(((uint32 *)&workRAM[address & 0x3FFFC]), value);
    break;      \
  case 0x03:    \
      WRITE32LE(((uint32 *)&internalRAM[address & 0x7ffC]), value);     \
    break;      \
  case 0x04:    \
    if(address < 0x4000400) {   \
      CPUUpdateRegister((address & 0x3FC), value & 0xFFFF);     \
      CPUUpdateRegister((address & 0x3FC) + 2, (value >> 16));  \
    }   \
    break;      \
  case 0x05:    \
    WRITE32LE(((uint32 *)&paletteRAM[address & 0x3FC]), value); \
    break;      \
  case 0x06:    \
    address = (address & 0x1fffc);
    if (((DISPCNT & 7) >2) && ((address & 0x1C000) == 0x18000))
     return;
    if ((address & 0x18000) == 0x18000)
     address &= 0x17fff;
    WRITE32LE(((uint32 *)&vram[address]), value);
    break;      \

  case 0x07:
    WRITE32LE(((uint32 *)&oam[address & 0x3fc]), value);
    break;

  case 0x0D:
    if(cpuEEPROMEnabled)
    {
     eepromWrite(address, value);
     break;
    }
    break;

  case 0x0E:
    FLASH_SRAM_Write(address, value);
    break;

  default: break;
 }
}

void CPUWriteHalfWord(uint32 address, uint16 value)
{
 switch(address >> 24)
 {
  case 2:
      WRITE16LE(((uint16 *)&workRAM[address & 0x3FFFE]),value);
    break;
  case 3:
      WRITE16LE(((uint16 *)&internalRAM[address & 0x7ffe]), value);
    break;
  case 4:
    if(address < 0x4000400)
      CPUUpdateRegister(address & 0x3fe, value);
    else goto unwritable;
    break;
  case 5:
    WRITE16LE(((uint16 *)&paletteRAM[address & 0x3fe]), value);
    break;
  case 6:
     address = (address & 0x1fffe);
     if (((DISPCNT & 7) >2) && ((address & 0x1C000) == 0x18000))
      return;
     if ((address & 0x18000) == 0x18000)
      address &= 0x17fff;
     WRITE16LE(((uint16 *)&vram[address]), value);
    break;
  case 7:
    WRITE16LE(((uint16 *)&oam[address & 0x3fe]), value);
    break;
  case 8:
  case 9:
    if(GBA_RTC && (address == 0x80000c4 || address == 0x80000c6 || address == 0x80000c8))
     GBA_RTC->Write(address, value);
    else
     goto unwritable;
    break;
  case 13:
    if(cpuEEPROMEnabled)
    {
     eepromWrite(address, (uint8)value);
     break;
    }
    goto unwritable;

  case 0x0E:
    FLASH_SRAM_Write(address, value);
    break;

  default:
  unwritable:
    break;
 }
}

void CPUWriteByte(uint32 address, uint8 b)
{
 switch(address >> 24)
 {
  case 2:
      workRAM[address & 0x3FFFF] = b;
      break;

  case 3:
      internalRAM[address & 0x7fff] = b;
      break;

  case 4:
    if(address < 0x4000400)
    {
     switch(address & 0x3FF)
     {
      case 0x301:
        if(b == 0x80)
         stopState = true;
        holdState = 1;
        holdType = -1;
        cpuNextEvent = cpuTotalTicks;
        break;

      case 0x60:
      case 0x61:
      case 0x62:
      case 0x63:
      case 0x64:
      case 0x65:
      case 0x68:
      case 0x69:
      case 0x6c:
      case 0x6d:
      case 0x70:
      case 0x71:
      case 0x72:
      case 0x73:
      case 0x74:
      case 0x75:
      case 0x78:
      case 0x79:
      case 0x7c:
      case 0x7d:
      case 0x80:
      case 0x81:
      case 0x84:
      case 0x85:
      case 0x90:
      case 0x91:
      case 0x92:
      case 0x93:
      case 0x94:
      case 0x95:
      case 0x96:
      case 0x97:
      case 0x98:
      case 0x99:
      case 0x9a:
      case 0x9b:
      case 0x9c:
      case 0x9d:
      case 0x9e:
      case 0x9f:
        soundEvent(address&0xFF, b);
        break;
      default:
        if(address & 1)
         CPUUpdateRegister(address & 0x3fe,
           ((READ16LE(((uint16 *)&ioMem[address & 0x3fe])))
           & 0x00FF) |
           b<<8);
        else
         CPUUpdateRegister(address & 0x3fe,
           ((READ16LE(((uint16 *)&ioMem[address & 0x3fe])) & 0xFF00) | b));
      }
      break;
    } else goto unwritable;
    break;
  case 5:
    // no need to switch
    *((uint16 *)&paletteRAM[address & 0x3FE]) = (b << 8) | b;
    break;
  case 6:
    address = (address & 0x1fffe);
    if (((DISPCNT & 7) >2) && ((address & 0x1C000) == 0x18000))
     return;
    if ((address & 0x18000) == 0x18000)
     address &= 0x17fff;
    // no need to switch
    // byte writes to OBJ VRAM are ignored
    if ((address) < objTilesAddress[((DISPCNT&7)+1)>>2])
     *((uint16 *)&vram[address]) = (b << 8) | b;
    break;
  case 7:
    // no need to switch
    // byte writes to OAM are ignored
    //    *((uint16 *)&oam[address & 0x3FE]) = (b << 8) | b;
    break;

  case 0xD:
    if(cpuEEPROMEnabled) {
      eepromWrite(address, b);
      break;
    }
    goto unwritable;

  case 0xE:
    FLASH_SRAM_Write(address, b);
    break;

  // default
  default:
    unwritable:
    break;
 }
}

uint8 cpuBitsSet[256];
uint8 cpuLowestBitSet[256];

static bool CPUInit(const std::string bios_fn)
{
 FILE *memfp;

 FlashSizeSet = FALSE;

 cpuSramEnabled = true;
 cpuFlashEnabled = true;
 cpuEEPROMEnabled = true;
 cpuEEPROMSensorEnabled = true;

 memfp = fopen(MDFN_MakeFName(MDFNMKF_SAV, 0, "type").c_str(), "rb");
 if(memfp)
 {
  char linebuffer[256];

  cpuSramEnabled = FALSE;
  cpuFlashEnabled = FALSE;
  cpuEEPROMEnabled = FALSE;
  cpuEEPROMSensorEnabled = FALSE;

  while(fgets(linebuffer, 256, memfp))
  {
   char args[2][256];
   int acount = sscanf(linebuffer, "%255s %255s", args[0], args[1]);

   if(acount < 1)
    continue;

   //MDFN_printf(_("Backup memory type override: %s %s\n"), linebuffer, (acount > 1) ? args[1] : "");

   if(!strcasecmp(args[0], "sram"))
   {
    cpuSramEnabled = TRUE;
   }
   else if(!strcasecmp(args[0], "flash"))
   {
    cpuFlashEnabled = TRUE;
    if(acount == 2)
    {
     int size_temp = atoi(args[1]);

     if(size_temp == 0x10000 || size_temp == 0x20000)
     {
      flashSetSize(size_temp);
      FlashSizeSet = TRUE;
     }
     else if(size_temp == 64 || size_temp == 128)
     {
      flashSetSize(size_temp * 1024);
      FlashSizeSet = TRUE;
     }
     else
      puts("Flash size error");
    }
   }
   else if(!strcasecmp(args[0], "eeprom"))
    cpuEEPROMEnabled = TRUE;
   else if(!strcasecmp(args[0], "sensor"))
    cpuEEPROMSensorEnabled = TRUE;
   else if(!strcasecmp(args[0], "rtc"))
    GBA_RTC = new RTC();
  }
  fclose(memfp);
 }

 useBios = false;

 if(bios_fn != "" && bios_fn != "0" && bios_fn != "none")
 {
  static const FileExtensionSpecStruct KnownBIOSExtensions[] =
  {
   { ".gba", "GameBoy Advance ROM Image" },
   { ".agb", "GameBoy Advance ROM Image" },
   { ".bin", "GameBoy Advance ROM Image" },
   { ".bios", "BIOS Image" },
   { NULL, NULL }
  };

  MDFNFILE bios_fp;

  if(bios_fp.Open(MDFN_MakeFName(MDFNMKF_FIRMWARE, 0, bios_fn.c_str()), KnownBIOSExtensions, _("GBA BIOS")))
  {
   if(GET_FSIZE(bios_fp) == 0x4000)
   {
    memcpy(bios, GET_FDATA(bios_fp), 0x4000);
    useBios = true;
   }
   else
    log_cb(RETRO_LOG_WARN, "Invalid BIOS file size.\n");
   bios_fp.Close();
  }
  else
   log_cb(RETRO_LOG_WARN, "Cannot find GBA bios file. Using high-level bios emulation.\n");
 }

 if(!useBios)
 {
  memcpy(bios, myROM, sizeof(myROM));
  Endian_A32_NE_to_LE(bios, sizeof(myROM) / 4);
 }

  int i = 0;

  biosProtected[0] = 0x00;
  biosProtected[1] = 0xf0;
  biosProtected[2] = 0x29;
  biosProtected[3] = 0xe1;

  for(i = 0; i < 256; i++) {
    int count = 0;
    int j;
    for(j = 0; j < 8; j++)
      if(i & (1 << j))
        count++;
    cpuBitsSet[i] = count;

    for(j = 0; j < 8; j++)
      if(i & (1 << j))
        break;
    cpuLowestBitSet[i] = j;
  }

  for(i = 0; i < 0x400; i++)
    ioReadable[i] = true;
  for(i = 0x10; i < 0x48; i++)
    ioReadable[i] = false;
  for(i = 0x4c; i < 0x50; i++)
    ioReadable[i] = false;
  for(i = 0x54; i < 0x60; i++)
    ioReadable[i] = false;
  for(i = 0x8c; i < 0x90; i++)
    ioReadable[i] = false;
  for(i = 0xa0; i < 0xb8; i++)
    ioReadable[i] = false;
  for(i = 0xbc; i < 0xc4; i++)
    ioReadable[i] = false;
  for(i = 0xc8; i < 0xd0; i++)
    ioReadable[i] = false;
  for(i = 0xd4; i < 0xdc; i++)
    ioReadable[i] = false;
  for(i = 0xe0; i < 0x100; i++)
    ioReadable[i] = false;
  for(i = 0x110; i < 0x120; i++)
    ioReadable[i] = false;
  for(i = 0x12c; i < 0x130; i++)
    ioReadable[i] = false;
  for(i = 0x138; i < 0x140; i++)
    ioReadable[i] = false;
  for(i = 0x144; i < 0x150; i++)
    ioReadable[i] = false;
  for(i = 0x15c; i < 0x200; i++)
    ioReadable[i] = false;
  for(i = 0x20c; i < 0x300; i++)
    ioReadable[i] = false;
  for(i = 0x304; i < 0x400; i++)
    ioReadable[i] = false;

  if(romSize < 0x1fe2000) {
    *((uint16 *)&rom[0x1fe209c]) = 0xdffa; // SWI 0xFA
    *((uint16 *)&rom[0x1fe209e]) = 0x4770; // BX LR
  } else {

  }
 return(1);
}

static void CPUReset(void) MDFN_COLD;
static void CPUReset(void)
{
  if(GBA_RTC)
   GBA_RTC->Reset();

  // clean registers
  memset(&reg[0], 0, sizeof(reg));
  // clean OAM
  memset(oam, 0, 0x400);
  // clean palette
  memset(paletteRAM, 0, 0x400);
  // clean vram
  memset(vram, 0, 0x20000);
  // clean io memory
  memset(ioMem, 0, 0x400);

  memset(internalRAM, 0, 0x8000);

  memset(workRAM, 0x00, 0x40000);

  DISPCNT  = 0x0080;
  DISPSTAT = 0x0000;
  VCOUNT   = (useBios && !skipBios) ? 0 :0x007E;
  BG0CNT   = 0x0000;
  BG1CNT   = 0x0000;
  BG2CNT   = 0x0000;
  BG3CNT   = 0x0000;

  for(int i = 0; i < 4; i++)
  {
   BGHOFS[i] = 0;
   BGVOFS[i] = 0;
  }

  BG2PA    = 0x0100;
  BG2PB    = 0x0000;
  BG2PC    = 0x0000;
  BG2PD    = 0x0100;
  BG2X_L   = 0x0000;
  BG2X_H   = 0x0000;
  BG2Y_L   = 0x0000;
  BG2Y_H   = 0x0000;
  BG3PA    = 0x0100;
  BG3PB    = 0x0000;
  BG3PC    = 0x0000;
  BG3PD    = 0x0100;
  BG3X_L   = 0x0000;
  BG3X_H   = 0x0000;
  BG3Y_L   = 0x0000;
  BG3Y_H   = 0x0000;
  WIN0H    = 0x0000;
  WIN1H    = 0x0000;
  WIN0V    = 0x0000;
  WIN1V    = 0x0000;
  WININ    = 0x0000;
  WINOUT   = 0x0000;
  MOSAIC   = 0x0000;
  BLDMOD   = 0x0000;
  COLEV    = 0x0000;
  COLY     = 0x0000;

  for(int i = 0; i < 4; i++)
   DMSAD_L[i] = DMSAD_H[i] = 0;

  for(int i = 0; i < 4; i++)
  {
   timers[i].D     = 0;
   timers[i].CNT   = 0;
  }

  P1       = 0x03FF;
  IE       = 0x0000;
  IF       = 0x0000;
  IME      = 0x0000;

  armMode = 0x1F;

  if(cpuIsMultiBoot) {
    reg[13].I = 0x03007F00;
    reg[15].I = 0x02000000;
    reg[16].I = 0x00000000;
    reg[R13_IRQ].I = 0x03007FA0;
    reg[R13_SVC].I = 0x03007FE0;
    armIrqEnable = true;
  } else {
    if(useBios && !skipBios) {
      reg[15].I = 0x00000000;
      armMode = 0x13;
      armIrqEnable = false;
    } else {
      reg[13].I = 0x03007F00;
      reg[15].I = 0x08000000;
      reg[16].I = 0x00000000;
      reg[R13_IRQ].I = 0x03007FA0;
      reg[R13_SVC].I = 0x03007FE0;
      armIrqEnable = true;
    }
  }
  armState = true;
  C_FLAG = false;
  V_FLAG = false;
  N_FLAG = false;
  Z_FLAG = false;

  UPDATE_REG(0x00, DISPCNT);
  UPDATE_REG(0x06, VCOUNT);
  UPDATE_REG(0x20, BG2PA);
  UPDATE_REG(0x26, BG2PD);
  UPDATE_REG(0x30, BG3PA);
  UPDATE_REG(0x36, BG3PD);
  UPDATE_REG(0x130, P1);
  UPDATE_REG(0x88, 0x200);

  // disable FIQ
  reg[16].I |= 0x40;

  CPUUpdateCPSR();

  armNextPC = reg[15].I;
  reg[15].I += 4;

  // reset internal state
  holdState = false;
  holdType = 0;

  biosProtected[0] = 0x00;
  biosProtected[1] = 0xf0;
  biosProtected[2] = 0x29;
  biosProtected[3] = 0xe1;

  lcdTicks = (useBios && !skipBios) ? 1008 : 208;

  for(int i = 0; i < 4; i++)
  {
   timers[i].On = false;
   timers[i].Ticks = 0;
   timers[i].Reload = 0;
   timers[i].ClockReload  = 0;
  }

  dmaSource[0] = 0;
  dmaDest[0] = 0;
  dmaSource[1] = 0;
  dmaDest[1] = 0;
  dmaSource[2] = 0;
  dmaDest[2] = 0;
  dmaSource[3] = 0;
  dmaDest[3] = 0;

  renderLine = mode0RenderLine;
  fxOn = false;
  windowOn = false;
  saveType = 0;
  layerEnable = DISPCNT & layerSettings;

  CPUUpdateRenderBuffers(true);

  for(int i = 0; i < 256; i++) {
    map[i].address = (uint8 *)&dummyAddress;
    map[i].mask = 0;
  }

  map[0].address = bios;
  map[0].mask = 0x3FFF;
  map[2].address = workRAM;
  map[2].mask = 0x3FFFF;
  map[3].address = internalRAM;
  map[3].mask = 0x7FFF;
  map[4].address = ioMem;
  map[4].mask = 0x3FF;
  map[5].address = paletteRAM;
  map[5].mask = 0x3FF;
  map[6].address = vram;
  map[6].mask = 0x1FFFF;
  map[7].address = oam;
  map[7].mask = 0x3FF;
  map[8].address = rom;
  map[8].mask = 0x1FFFFFF;
  map[9].address = rom;
  map[9].mask = 0x1FFFFFF;
  map[10].address = rom;
  map[10].mask = 0x1FFFFFF;
  map[12].address = rom;
  map[12].mask = 0x1FFFFFF;
  map[14].address = flashSaveMemory;
  map[14].mask = 0xFFFF;

  eepromReset();
  GBA_Flash_Reset();

  soundReset();

  CPUUpdateWindow0();
  CPUUpdateWindow1();

  // make sure registers are correctly initialized if not using BIOS
  if(!useBios) {
    if(cpuIsMultiBoot)
      BIOS_RegisterRamReset(0xfe);
    else
      BIOS_RegisterRamReset(0xff);
  } else {
    if(cpuIsMultiBoot)
      BIOS_RegisterRamReset(0xfe);
  }

  ARM_PREFETCH;

  cpuDmaHack = false;

  SWITicks = 0;
}

void CPUInterrupt()
{
  uint32 PC = reg[15].I;
  bool savedState = armState;
  CPUSwitchMode(0x12, true, false);
  reg[14].I = PC;
  if(!savedState)
    reg[14].I += 2;
  reg[15].I = 0x18;
  armState = true;
  armIrqEnable = false;

  armNextPC = reg[15].I;
  reg[15].I += 4;
  ARM_PREFETCH;

  //  if(!holdState)
  biosProtected[0] = 0x02;
  biosProtected[1] = 0xc0;
  biosProtected[2] = 0x5e;
  biosProtected[3] = 0xe5;
}

uint32 soundTS = 0;
static uint8 *padq;

static void SetInput(unsigned port, const char *type, void *ptr)
{
 padq = (uint8*)ptr;
}

int32 MDFNGBA_GetTimerPeriod(int which)
{
 int32 ret = ((0x10000 - timers[which].Reload) << timers[which].ClockReload);
// printf("%d, %08x\n", ret, timers[which].Reload);
 return(ret);
}

static int frameready;
static int HelloSkipper;

static void CPULoop(EmulateSpecStruct* espec, int ticks)
{
  MDFN_Surface* surface = espec->surface;
  int clockTicks;
  int timerOverflow = 0;
  // variable used by the CPU core
  cpuTotalTicks = 0;
  cpuBreakLoop = false;
  cpuNextEvent = CPUUpdateTicks();
  if(cpuNextEvent > ticks)
    cpuNextEvent = ticks;


  for(;;) {
    if(!holdState && !SWITicks) {
      if(armState) {
        clockTicks = RunARM();
      } else {
        clockTicks = RunTHUMB();
      }
    } else
      clockTicks = CPUUpdateTicks();

    cpuTotalTicks += clockTicks;

    if(cpuTotalTicks >= cpuNextEvent) {
      int remainingTicks = cpuTotalTicks - cpuNextEvent;

      if (SWITicks)
      {
        SWITicks-=clockTicks;
        if (SWITicks<0)
          SWITicks = 0;
      }

      clockTicks = cpuNextEvent;
      cpuTotalTicks = 0;
      cpuDmaHack = false;

updateLoop:

      if (IRQTicks)
      {
        IRQTicks -= clockTicks;
        if (IRQTicks<0)
          IRQTicks = 0;
      }
      soundTS += clockTicks;
      lcdTicks -= clockTicks;

      if(lcdTicks <= 0) {
        if(DISPSTAT & 1) { // V-BLANK
          // if in V-Blank mode, keep computing...
          if(DISPSTAT & 2) {
            lcdTicks += 1008;
            VCOUNT++;
            UPDATE_REG(0x06, VCOUNT);
            DISPSTAT &= 0xFFFD;
            UPDATE_REG(0x04, DISPSTAT);
            CPUCompareVCOUNT();
          } else {
            lcdTicks += 224;
            DISPSTAT |= 2;
            UPDATE_REG(0x04, DISPSTAT);
            if(DISPSTAT & 16) {
              IF |= 2;
              UPDATE_REG(0x202, IF);
            }
          }

          if(VCOUNT >= 228) { //Reaching last line
            DISPSTAT &= 0xFFFC;
            UPDATE_REG(0x04, DISPSTAT);
            VCOUNT = 0;
            UPDATE_REG(0x06, VCOUNT);
            CPUCompareVCOUNT();
          }
        } else {
          if(DISPSTAT & 2) {
            // if in H-Blank, leave it and move to drawing mode
            VCOUNT++;
            UPDATE_REG(0x06, VCOUNT);

            lcdTicks += 1008;
            DISPSTAT &= 0xFFFD;
            if(VCOUNT == 160) {
              //ticks = 0;
              //puts("VBlank");
              uint32 joy = padbufblah;
              P1 = 0x03FF ^ (joy & 0x3FF);
              //if(cpuEEPROMSensorEnabled)
                //systemUpdateMotionSensor();
              UPDATE_REG(0x130, P1);
              uint16 P1CNT = READ16LE(((uint16 *)&ioMem[0x132]));
              // this seems wrong, but there are cases where the game
              // can enter the stop state without requesting an IRQ from
              // the joypad.
              if((P1CNT & 0x4000) || stopState) {
                uint16 p1 = (0x3FF ^ P1) & 0x3FF;
                if(P1CNT & 0x8000) {
                  if(p1 == (P1CNT & 0x3FF)) {
                    IF |= 0x1000;
                    UPDATE_REG(0x202, IF);
                  }
                } else {
                  if(p1 & P1CNT) {
                    IF |= 0x1000;
                    UPDATE_REG(0x202, IF);
                  }
                }
              }

              DISPSTAT |= 1;
              DISPSTAT &= 0xFFFD;
              UPDATE_REG(0x04, DISPSTAT);
              if(DISPSTAT & 0x0008) {
                IF |= 1;
                UPDATE_REG(0x202, IF);
              }
              CPUCheckDMA(1, 0x0f);
            }

            UPDATE_REG(0x04, DISPSTAT);
            CPUCompareVCOUNT();

          } else {
            if(!HelloSkipper) {
              //printf("RL: %d\n", VCOUNT);
              const uint32 *src = lineMix;

              (*renderLine)();

              if(surface->format.bpp == 32) {
                const uint32* cm = systemColorMap->v32;
                uint32 *dest = surface->pixels + VCOUNT * surface->pitch32;

                for(int x = 120; x; x--)
                {
                  *dest = cm[*src & 0xFFFF];
                  dest++;
                  src++;
                  *dest = cm[*src & 0xFFFF];
                  dest++;
                  src++;
                }
              } else {
                const uint16* cm = systemColorMap->v16;
                uint16* dest = surface->pixels16 + VCOUNT * surface->pitchinpix;

                for(int x = 0; x < 240; x += 2)
                {
                  dest[x + 0] = cm[(uint16)src[x + 0]];
                  dest[x + 1] = cm[(uint16)src[x + 1]];
                }
              }
              MDFN_MidLineUpdate(espec, VCOUNT);
            }
            // entering H-Blank
            DISPSTAT |= 2;
            UPDATE_REG(0x04, DISPSTAT);
            lcdTicks += 224;
            CPUCheckDMA(2, 0x0f);
            if(DISPSTAT & 16) {
              IF |= 2;
              UPDATE_REG(0x202, IF);
            }
            if(VCOUNT == 159) {
              frameready = 1;
              cpuBreakLoop = 1;
            }
          }
        }
      }

      if(!stopState) {
        if(timers[0].On) {
          timers[0].Ticks -= clockTicks;
          if(timers[0].Ticks <= 0) {
            timers[0].Ticks += (0x10000 - timers[0].Reload) << timers[0].ClockReload;
            timerOverflow |= 1;
            soundTimerOverflow(0);
            if(timers[0].CNT & 0x40) {
              IF |= 0x08;
              UPDATE_REG(0x202, IF);
            }
          }
          timers[0].D = 0xFFFF - (timers[0].Ticks >> timers[0].ClockReload);
          UPDATE_REG(0x100, timers[0].D);
        }

        if(timers[1].On) {
          if(timers[1].CNT & 4) {
            if(timerOverflow & 1) {
              timers[1].D++;
              if(timers[1].D == 0) {
                timers[1].D += timers[1].Reload;
                timerOverflow |= 2;
                soundTimerOverflow(1);
                if(timers[1].CNT & 0x40) {
                  IF |= 0x10;
                  UPDATE_REG(0x202, IF);
                }
              }
              UPDATE_REG(0x104, timers[1].D);
            }
          } else {
            timers[1].Ticks -= clockTicks;
            if(timers[1].Ticks <= 0) {
              timers[1].Ticks += (0x10000 - timers[1].Reload) << timers[1].ClockReload;
              timerOverflow |= 2;
              soundTimerOverflow(1);
              if(timers[1].CNT & 0x40) {
                IF |= 0x10;
                UPDATE_REG(0x202, IF);
              }
            }
            timers[1].D = 0xFFFF - (timers[1].Ticks >> timers[1].ClockReload);
            UPDATE_REG(0x104, timers[1].D);
          }
        }

        if(timers[2].On) {
          if(timers[2].CNT & 4) {
            if(timerOverflow & 2) {
              timers[2].D++;
              if(timers[2].D == 0) {
                timers[2].D += timers[2].Reload;
                timerOverflow |= 4;
                if(timers[2].CNT & 0x40) {
                  IF |= 0x20;
                  UPDATE_REG(0x202, IF);
                }
              }
              UPDATE_REG(0x108, timers[2].D);
            }
          } else {
            timers[2].Ticks -= clockTicks;
            if(timers[2].Ticks <= 0) {
              timers[2].Ticks += (0x10000 - timers[2].Reload) << timers[2].ClockReload;
              timerOverflow |= 4;
              if(timers[2].CNT & 0x40) {
                IF |= 0x20;
                UPDATE_REG(0x202, IF);
              }
            }
            timers[2].D = 0xFFFF - (timers[2].Ticks >> timers[2].ClockReload);
            UPDATE_REG(0x108, timers[2].D);
          }
        }

        if(timers[3].On) {
          if(timers[3].CNT & 4) {
            if(timerOverflow & 4) {
              timers[3].D++;
              if(timers[3].D == 0) {
                timers[3].D += timers[3].Reload;
                if(timers[3].CNT & 0x40) {
                  IF |= 0x40;
                  UPDATE_REG(0x202, IF);
                }
              }
              UPDATE_REG(0x10C, timers[3].D);
            }
          } else {
              timers[3].Ticks -= clockTicks;
            if(timers[3].Ticks <= 0) {
              timers[3].Ticks += (0x10000 - timers[3].Reload) << timers[3].ClockReload;
              if(timers[3].CNT & 0x40) {
                IF |= 0x40;
                UPDATE_REG(0x202, IF);
              }
            }
            timers[3].D = 0xFFFF - (timers[3].Ticks >> timers[3].ClockReload);
            UPDATE_REG(0x10C, timers[3].D);
          }
        }
      }

      timerOverflow = 0;

      ticks -= clockTicks;

      cpuNextEvent = CPUUpdateTicks();

      if(cpuDmaTicksToUpdate > 0) {
        if(cpuDmaTicksToUpdate > cpuNextEvent)
          clockTicks = cpuNextEvent;
        else
          clockTicks = cpuDmaTicksToUpdate;
        cpuDmaTicksToUpdate -= clockTicks;
        if(cpuDmaTicksToUpdate < 0)
          cpuDmaTicksToUpdate = 0;
        cpuDmaHack = true;
        goto updateLoop;
      }

      if(IF && (IME & 1) && armIrqEnable) {
        int res = IF & IE;
        if(stopState)
          res &= 0x3080;
        if(res) {
          if (intState)
          {
            if (!IRQTicks)
            {
              CPUInterrupt();
              intState = false;
              holdState = false;
              stopState = false;
              holdType = 0;
            }
          }
          else
          {
            if (!holdState)
            {
              intState = true;
              IRQTicks=7;
              if (cpuNextEvent> IRQTicks)
                cpuNextEvent = IRQTicks;
            }
            else
            {
              CPUInterrupt();
              holdState = false;
              stopState = false;
              holdType = 0;
            }
          }

          // Stops the SWI Ticks emulation if an IRQ is executed
          //(to avoid problems with nested IRQ/SWI)
          if (SWITicks)
            SWITicks = 0;
        }
      }

      if(remainingTicks > 0) {
        if(remainingTicks > cpuNextEvent)
          clockTicks = cpuNextEvent;
        else
          clockTicks = remainingTicks;
        remainingTicks -= clockTicks;
        if(remainingTicks < 0)
          remainingTicks = 0;
        goto updateLoop;
      }

      if (timerOnOffDelay)
          applyTimer();

      if(cpuNextEvent > ticks)
        cpuNextEvent = ticks;

      if(ticks <= 0 || cpuBreakLoop)
        break;

    }
  }
}

static void Emulate(EmulateSpecStruct *espec)
{
 espec->DisplayRect.x = 0;
 espec->DisplayRect.y = 0;
 espec->DisplayRect.w = 240;
 espec->DisplayRect.h = 160;

#if 0
 {
  static bool firstcat = true;
  MDFN_PixelFormat nf;

  nf.bpp = 16;
  nf.colorspace = MDFN_COLORSPACE_RGB;
  nf.Rshift = 11;
  nf.Gshift = 5;
  nf.Bshift = 0;
  nf.Ashift = 16;

  nf.Rprec = 5;
  nf.Gprec = 5;
  nf.Bprec = 5;
  nf.Aprec = 8;

  espec->surface->SetFormat(nf, false);
  espec->VideoFormatChanged = firstcat;
  firstcat = false;
 }
#endif

 if(espec->VideoFormatChanged)
  RedoColorMap(espec->surface->format); //espec->surface->format.Rshift, espec->surface->format.Gshift, espec->surface->format.Bshift);

 if(espec->SoundFormatChanged)
  MDFNGBA_SetSoundRate(espec->SoundRate);

 #if 0
 int cursong = workRAM[0x2020c96- (0x2 << 24)];
 static int last_song = 0;

 if(cursong != last_song)
 {
  if(last_song == 250)
  {
   MDFNI_EndWaveRecord();
   exit(1);
  }
  else
  {
   char wavepath[256];
   if(last_song != 0)
    MDFNI_EndWaveRecord();
   trio_snprintf(wavepath, 256, "/meow/mother3-%d.wav", cursong);
   MDFNI_BeginWaveRecord(FSettings.SndRate, 2, wavepath);
  }
  last_song = cursong;
 }
 #endif

 padbufblah = padq[0] | (padq[1] << 8);

 frameready = 0;

 HelloSkipper = espec->skip;

 MDFNMP_ApplyPeriodicCheats();

 while(!frameready && (soundTS < 300000))
  CPULoop(espec, 300000);

 if(GBA_RTC)
  GBA_RTC->AddTime(soundTS);

 espec->MasterCycles = soundTS;

 espec->SoundBufSize = MDFNGBASOUND_Flush(espec->SoundBuf, espec->SoundBufMaxSize);
}
static void SetLayerEnableMask(uint64 mask)
{
 layerSettings = mask << 8;
 layerEnable = layerSettings & DISPCNT;

 CPUUpdateRender();
 CPUUpdateRenderBuffers(true);
 CPUUpdateWindow0();
 CPUUpdateWindow1();
}

static void DoSimpleCommand(int cmd)
{
 switch(cmd)
 {
  case MDFN_MSC_POWER:
  case MDFN_MSC_RESET: CPUReset(); break;
 }
}

static MDFNSetting GBASettings[] =
{
 { "gba.bios", 	MDFNSF_EMU_STATE,	"Path to optional GBA BIOS ROM image.", NULL, MDFNST_STRING, "" },
 { NULL }
};

static const InputDeviceInputInfoStruct IDII[] =
{
 { "a", "A", 		/*VIRTB_1,*/ 7, IDIT_BUTTON_CAN_RAPID, NULL },

 { "b", "B", 		/*VIRTB_0,*/ 6, IDIT_BUTTON_CAN_RAPID, NULL },

 { "select", "SELECT", 	/*VIRTB_SELECT,*/ 4, IDIT_BUTTON, NULL },

 { "start", "START", 	/*VIRTB_START,*/ 5, IDIT_BUTTON, NULL },

 { "right", "RIGHT →", 	/*VIRTB_DP0_R,*/ 3, IDIT_BUTTON, "left" },

 { "left", "LEFT ←", 	/*VIRTB_DP0_L,*/ 2, IDIT_BUTTON, "right" },

 { "up", "UP ↑", 	/*VIRTB_DP0_U,*/ 0, IDIT_BUTTON, "down" },

 { "down", "DOWN ↓",	/*VIRTB_DP0_D,*/ 1, IDIT_BUTTON, "up" },

 { "shoulder_r", "SHOULDER R", /*VIRTB_SHLDR_L,*/	9, IDIT_BUTTON, NULL },

 { "shoulder_l", "SHOULDER L", /*VIRTB_SHLDR_R,*/	8, IDIT_BUTTON, NULL },
};

static InputDeviceInfoStruct InputDeviceInfo[] =
{
 {
  "gamepad",
  "Gamepad",
  NULL,
  NULL,
  sizeof(IDII) / sizeof(InputDeviceInputInfoStruct),
  IDII,
 }
};

static const InputPortInfoStruct PortInfo[] =
{
 { "builtin", "Built-In", sizeof(InputDeviceInfo) / sizeof(InputDeviceInfoStruct), InputDeviceInfo, "gamepad" }
};

static InputInfoStruct InputInfo =
{
 sizeof(PortInfo) / sizeof(InputPortInfoStruct),
 PortInfo
};

static const FileExtensionSpecStruct KnownExtensions[] =
{
 { ".gsf", "GSF Rip" },
 { ".minigsf", "MiniGSF Rip" },
 { ".gba", "GameBoy Advance ROM Image" },
 { ".agb", "GameBoy Advance ROM Image" },
 { ".bin", "GameBoy Advance ROM Image" },
 { NULL, NULL }
};

MDFNGI EmulatedGBA =
{
 GBASettings,
 MDFN_MASTERCLOCK_FIXED(16777216),
 (uint32)((double)4194304 / 70224 * 65536 * 256),

 false, // Multires possible?

 240,   // lcm_width
 160,   // lcm_height
 NULL,  // Dummy

 240,	// Nominal width
 160,	// Nominal height

 240,	// Framebuffer width
 160,	// Framebuffer height

 2,	// Number of output sound channels
};


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

#ifdef NEED_DEINTERLACER
static bool PrevInterlaced;
static Deinterlacer deint;
#endif

#define MEDNAFEN_CORE_NAME_MODULE "gba"
#define MEDNAFEN_CORE_NAME "Mednafen VBA-M"
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

const char *mednafen_core_str = MEDNAFEN_CORE_NAME;

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

   MDFNI_InitializeModule();

   const char *dir = NULL;

   if (environ_cb(RETRO_ENVIRONMENT_GET_SYSTEM_DIRECTORY, &dir) && dir)
   {
      retro_base_directory = dir;
      // Make sure that we don't have any lingering slashes, etc, as they break Windows.
      size_t last = retro_base_directory.find_last_not_of("/\\");
      if (last != std::string::npos)
         last++;

      retro_base_directory = retro_base_directory.substr(0, last);

      MDFNI_Initialize(retro_base_directory.c_str());
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

static void set_volume (uint32_t *ptr, unsigned number)
{
   switch(number)
   {
      default:
         *ptr = number;
         break;
   }
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

   overscan = false;
   environ_cb(RETRO_ENVIRONMENT_GET_OVERSCAN, &overscan);

   set_basename(info->path);

   check_variables(true);

   MDFN_printf("Loading %s\n", info->path);
   game = MDFNI_LoadGame(MEDNAFEN_CORE_NAME_MODULE, (const uint8_t *)info->data, info->size);
   if (!game)
      return false;

   MDFN_PixelFormat pix_fmt(MDFN_COLORSPACE_RGB, 16, 8, 0, 24);
   memset(&last_pixel_format, 0, sizeof(MDFN_PixelFormat));

   surf = new MDFN_Surface(NULL, FB_WIDTH, FB_HEIGHT, FB_WIDTH, pix_fmt);

#ifdef NEED_DEINTERLACER
   PrevInterlaced = false;
   deint.ClearState();
#endif

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



// Hardcoded for PSX. No reason to parse lots of structures ...
// See mednafen/psx/input/gamepad.cpp
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
}

static uint64_t video_frames, audio_frames;


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
      spec.VideoFormatChanged = TRUE;

      last_pixel_format = spec.surface->format;
   }

   if (spec.SoundRate != last_sound_rate)
   {
      spec.SoundFormatChanged = true;
      last_sound_rate = spec.SoundRate;
   }

   Emulate(&spec);

#ifdef NEED_DEINTERLACER
   if (spec.InterlaceOn)
   {
      if (!PrevInterlaced)
         deint.ClearState();

      deint.Process(spec.surface, spec.DisplayRect, spec.LineWidths, spec.InterlaceField);

      PrevInterlaced = true;

      spec.InterlaceOn = false;
      spec.InterlaceField = 0;
   }
   else
      PrevInterlaced = false;
#endif

   int16 *const SoundBuf = spec.SoundBuf + spec.SoundBufSizeALMS * 2;
   int32 SoundBufSize = spec.SoundBufSize - spec.SoundBufSizeALMS;
   const int32 SoundBufMaxSize = spec.SoundBufMaxSize - spec.SoundBufSizeALMS;

   spec.SoundBufSize = spec.SoundBufSizeALMS + SoundBufSize;

   unsigned width  = spec.DisplayRect.w;
   unsigned height = spec.DisplayRect.h;

#if defined(WANT_32BPP)
   const uint32_t *pix = surf->pixels;
   video_cb(pix, width, height, FB_WIDTH << 2);
#elif defined(WANT_16BPP)
   const uint16_t *pix = surf->pixels16;
   video_cb(pix, width, height, FB_WIDTH << 1);
#endif

   video_frames++;
   audio_frames += spec.SoundBufSize;

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

   if (log_cb)
   {
      log_cb(RETRO_LOG_INFO, "[%s]: Samples / Frame: %.5f\n",
            mednafen_core_str, (double)audio_frames / video_frames);
      log_cb(RETRO_LOG_INFO, "[%s]: Estimated FPS: %.5f\n",
            mednafen_core_str, (double)video_frames * 44100 / audio_frames);
   }
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
      if (!use_mednafen_save_method)
         return libretro_save_buf;

   return NULL;
}

size_t retro_get_memory_size(unsigned type)
{
   if (type == RETRO_MEMORY_SAVE_RAM)
      if (!use_mednafen_save_method)
         return libretro_save_size;
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
      log_cb(RETRO_LOG_INFO, "MDFN_MakeFName: %s\n", ret.c_str());
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

void MDFND_MidSync(const EmulateSpecStruct *)
{}

void MDFN_MidLineUpdate(EmulateSpecStruct *espec, int y)
{
 //MDFND_MidLineUpdate(espec, y);
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
   MDFN_indent(1);
   MDFN_printf(_("Using module: gba\n\n"));
   MDFN_indent(1);

   if(Load(data, size) <= 0)
   {
      MDFN_indent(-2);
      MDFNGameInfo = NULL;
      return(0);
   }

   MDFN_LoadGameCheats(NULL);
   MDFNMP_InstallReadPatches();

   MDFN_ResetMessages();   // Save state, status messages, etc.

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

bool MDFNI_InitializeModule(void)
{
 return(1);
}

int MDFNI_Initialize(const char *basedir)
{
   return(1);
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
