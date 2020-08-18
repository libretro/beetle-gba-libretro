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

#ifdef WANT_CRC32
#include "scrc32.h"
#endif

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

static bool FlashSizeSet; // Set to true if explicitly set by the user
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

int hardware;

static const uint32 myROM[] =
{
 #include "myrom.h"
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

 ret &= MDFNSS_StateAction(sm, load, data_only, StateRegs, "MAIN", false);

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

 ret &= MDFNSS_StateAction(sm, load, data_only, RAMState, "RAM", false);

 if(cpuEEPROMEnabled)
  ret &= EEPROM_StateAction(sm, load, data_only);

 ret &= Flash_StateAction(sm, load, data_only);

 if(GBA_RTC)
  ret &= GBA_RTC->StateAction(sm, load, data_only);

 ret &= MDFNSS_StateAction(sm, load, data_only, Joy_StateRegs, "JOY", false);
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
  return(true);
 }
 return(false);
}

static bool CPUReadBatteryFile(const char *filename) MDFN_COLD;
static bool CPUReadBatteryFile(const char *filename)
{
 FILE *gp = gzopen(filename, "rb");
 long size;

 if(!gp)
  return(false);

 size = 0;
 while(gzgetc(gp) != EOF)
  size++;

 if(size == 512 || size == 0x2000) // Load the file as EEPROM for Mednafen < 0.8.2
 {
  gzclose(gp);

  if(cpuEEPROMEnabled)
  {
   puts("note:  Loading sav file as eeprom data");
   EEPROM_LoadFile(filename);
  }
  return(false);
 }

 gzseek(gp, 0, SEEK_SET);

 if(size == 0x20000)
 {
  if(gzread(gp, flashSaveMemory, 0x20000) != 0x20000)
  {
   gzclose(gp);
   return(false);
  }
  if(!FlashSizeSet)
  {
   flashSetSize(0x20000);
   FlashSizeSet = true;
  }
 }
 else
 {
  if(gzread(gp, flashSaveMemory, 0x10000) != 0x10000)
  {
   gzclose(gp);
   return(false);
  }
  if(!FlashSizeSet)
  {
   flashSetSize(0x10000);
   FlashSizeSet = true;
  }
 }
 gzclose(gp);
 return(true);
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

 Flash_Kill();

 if(GBA_RTC)
 {
  delete GBA_RTC;
  GBA_RTC = NULL;
 }
}

void CloseGame(void)
{
 if (use_mednafen_save_method)
 {
   EEPROM_SaveFile(MDFN_MakeFName(MDFNMKF_SAV, 0, "eep").c_str());
   CPUWriteBatteryFile(MDFN_MakeFName(MDFNMKF_SAV, 0, "sav").c_str());
 }

 // Call CPUCleanUp() to deallocate memory AFTER the backup memory is saved.
 CPUCleanUp();
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

int Load(const uint8_t *data, size_t size)
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
   md5.update(whereToLoad, size);
   md5.finish(MDFNGameInfo->MD5);

   MDFN_printf("\n");
   MDFN_printf(_("ROM:       %dKiB\n"), (size + 1023) / 1024);
#ifdef WANT_CRC32
   MDFN_printf(_("ROM CRC32: 0x%08x\n"), (unsigned int)crc32(0, whereToLoad, size));
#endif
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

  Flash_Init();
  eepromInit();

  if (use_mednafen_save_method)
  {
   // EEPROM might be loaded from within CPUReadBatteryFile for support for Mednafen < 0.8.2, so call before EEPROM_LoadFile(), which
   // is more specific...kinda.
   if(cpuSramEnabled || cpuFlashEnabled)
    CPUReadBatteryFile(MDFN_MakeFName(MDFNMKF_SAV, 0, "sav").c_str());

   if(cpuEEPROMEnabled)
    EEPROM_LoadFile(MDFN_MakeFName(MDFNMKF_SAV, 0, "eep").c_str());
  }

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
   cpuSramEnabled = false;
  else if((A & 0xFFFF) != 0x2AAA)
   cpuFlashEnabled = false;

  if(!cpuFlashEnabled || !cpuSramEnabled)
   MDFN_printf("%s emulation disabled by write to:  %08x %08x\n", cpuSramEnabled ? "FLASH" : "SRAM", A, V);
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

typedef struct  {
   char romtitle[256];
   char romid[5];
   int flashSize;
   int saveType;
   int rtcEnabled;
   int mirroringEnabled;
   int useBios;
} ini_t;

static const ini_t gbaover[256] = {
   //romtitle,							    	romid	flash	save	rtc	mirror	bios
   {"2 Games in 1 - Dragon Ball Z - The Legacy of Goku I & II (USA)",	"BLFE",	0,	1,	0,	0,	0},
   {"2 Games in 1 - Dragon Ball Z - Buu's Fury + Dragon Ball GT - Transformation (USA)", "BUFE", 0, 1, 0, 0, 0},
   {"Boktai - The Sun Is in Your Hand (Europe)(En,Fr,De,Es,It)",		"U3IP",	0,	0,	1,	0,	0},
   {"Boktai - The Sun Is in Your Hand (USA)",				"U3IE",	0,	0,	1,	0,	0},
   {"Boktai 2 - Solar Boy Django (USA)",					"U32E",	0,	0,	1,	0,	0},
   {"Boktai 2 - Solar Boy Django (Europe)(En,Fr,De,Es,It)",		"U32P",	0,	0,	1,	0,	0},
   {"Bokura no Taiyou - Taiyou Action RPG (Japan)",			"U3IJ",	0,	0,	1,	0,	0},
   {"Card e-Reader+ (Japan)",						"PSAJ",	131072,	0,	0,	0,	0},
   {"Classic NES Series - Bomberman (USA, Europe)",			"FBME",	0,	1,	0,	1,	0},
   {"Classic NES Series - Castlevania (USA, Europe)",			"FADE",	0,	1,	0,	1,	0},
   {"Classic NES Series - Donkey Kong (USA, Europe)",			"FDKE",	0,	1,	0,	1,	0},
   {"Classic NES Series - Dr. Mario (USA, Europe)",			"FDME",	0,	1,	0,	1,	0},
   {"Classic NES Series - Excitebike (USA, Europe)",			"FEBE",	0,	1,	0,	1,	0},
   {"Classic NES Series - Legend of Zelda (USA, Europe)",			"FZLE",	0,	1,	0,	1,	0},
   {"Classic NES Series - Ice Climber (USA, Europe)",			"FICE",	0,	1,	0,	1,	0},
   {"Classic NES Series - Metroid (USA, Europe)",				"FMRE",	0,	1,	0,	1,	0},
   {"Classic NES Series - Pac-Man (USA, Europe)",				"FP7E",	0,	1,	0,	1,	0},
   {"Classic NES Series - Super Mario Bros. (USA, Europe)",		"FSME",	0,	1,	0,	1,	0},
   {"Classic NES Series - Xevious (USA, Europe)",				"FXVE",	0,	1,	0,	1,	0},
   {"Classic NES Series - Zelda II - The Adventure of Link (USA, Europe)",	"FLBE",	0,	1,	0,	1,	0},
   {"Digi Communication 2 - Datou! Black Gemagema Dan (Japan)",		"BDKJ",	0,	1,	0,	0,	0},
   {"e-Reader (USA)",							"PSAE",	131072,	0,	0,	0,	0},
   {"Dragon Ball GT - Transformation (USA)",				"BT4E",	0,	1,	0,	0,	0},
   {"Dragon Ball Z - Buu's Fury (USA)",					"BG3E",	0,	1,	0,	0,	0},
   {"Dragon Ball Z - Taiketsu (Europe)(En,Fr,De,Es,It)",			"BDBP",	0,	1,	0,	0,	0},
   {"Dragon Ball Z - Taiketsu (USA)",					"BDBE",	0,	1,	0,	0,	0},
   {"Dragon Ball Z - The Legacy of Goku II International (Japan)",		"ALFJ",	0,	1,	0,	0,	0},
   {"Dragon Ball Z - The Legacy of Goku II (Europe)(En,Fr,De,Es,It)",	"ALFP", 0,	1,	0,	0,	0},
   {"Dragon Ball Z - The Legacy of Goku II (USA)",				"ALFE",	0,	1,	0,	0,	0},
   {"Dragon Ball Z - The Legacy Of Goku (Europe)(En,Fr,De,Es,It)",		"ALGP",	0,	1,	0,	0,	0},
   {"Dragon Ball Z - The Legacy of Goku (USA)",				"ALGE",	131072,	1,	0,	0,	0},
   {"F-Zero - Climax (Japan)",						"BFTJ",	131072,	0,	0,	0,	0},
   {"Famicom Mini Vol. 01 - Super Mario Bros. (Japan)",			"FMBJ",	0,	1,	0,	1,	0},
   {"Famicom Mini Vol. 12 - Clu Clu Land (Japan)",				"FCLJ",	0,	1,	0,	1,	0},
   {"Famicom Mini Vol. 13 - Balloon Fight (Japan)",			"FBFJ",	0,	1,	0,	1,	0},
   {"Famicom Mini Vol. 14 - Wrecking Crew (Japan)",			"FWCJ",	0,	1,	0,	1,	0},
   {"Famicom Mini Vol. 15 - Dr. Mario (Japan)",				"FDMJ",	0,	1,	0,	1,	0},
   {"Famicom Mini Vol. 16 - Dig Dug (Japan)",				"FTBJ",	0,	1,	0,	1,	0},
   {"Famicom Mini Vol. 17 - Takahashi Meijin no Boukenjima (Japan)",	"FTBJ",	0,	1,	0,	1,	0},
   {"Famicom Mini Vol. 18 - Makaimura (Japan)",				"FMKJ",	0,	1,	0,	1,	0},
   {"Famicom Mini Vol. 19 - Twin Bee (Japan)",				"FTWJ",	0,	1,	0,	1,	0},
   {"Famicom Mini Vol. 20 - Ganbare Goemon! Karakuri Douchuu (Japan)",	"FGGJ",	0,	1,	0,	1,	0},
   {"Famicom Mini Vol. 21 - Super Mario Bros. 2 (Japan)",			"FM2J",	0,	1,	0,	1,	0},
   {"Famicom Mini Vol. 22 - Nazo no Murasame Jou (Japan)",			"FNMJ",	0,	1,	0,	1,	0},
   {"Famicom Mini Vol. 23 - Metroid (Japan)",				"FMRJ",	0,	1,	0,	1,	0},
   {"Famicom Mini Vol. 24 - Hikari Shinwa - Palthena no Kagami (Japan)",	"FPTJ",	0,	1,	0,	1,	0},
   {"Famicom Mini Vol. 25 - The Legend of Zelda 2 - Link no Bouken (Japan)","FLBJ",0,	1,	0,	1,	0},
   {"Famicom Mini Vol. 26 - Famicom Mukashi Banashi - Shin Onigashima - Zen Kou Hen (Japan)","FFMJ",0,1,0,	1,	0},
   {"Famicom Mini Vol. 27 - Famicom Tantei Club - Kieta Koukeisha - Zen Kou Hen (Japan)","FTKJ",0,1,0,	1,	0},
   {"Famicom Mini Vol. 28 - Famicom Tantei Club Part II - Ushiro ni Tatsu Shoujo - Zen Kou Hen (Japan)","FTUJ",0,1,0,1,0},
   {"Famicom Mini Vol. 29 - Akumajou Dracula (Japan)",			"FADJ",	0,	1,	0,	1,	0},
   {"Famicom Mini Vol. 30 - SD Gundam World - Gachapon Senshi Scramble Wars (Japan)","FSDJ",0,1,	0,	1,	0},
   {"Game Boy Wars Advance 1+2 (Japan)",					"BGWJ",	131072,	0,	0,	0,	0},
   {"Golden Sun - The Lost Age (USA)",					"AGFE",	65536,	0,	0,	1,	0},
   {"Golden Sun (USA)",							"AGSE",	65536,	0,	0,	1,	0},
   {"Iridion II (Europe) (En,Fr,De)",							"AI2P",	0,	5,	0,	0,	0},
   {"Iridion II (USA)",							"AI2E",	0,	5,	0,	0,	0},
   {"Koro Koro Puzzle - Happy Panechu! (Japan)",				"KHPJ",	0,	4,	0,	0,	0},
   {"Mario vs. Donkey Kong (Europe)",					"BM5P",	0,	3,	0,	0,	0},
   {"Pocket Monsters - Emerald (Japan)",					"BPEJ",	131072,	0,	1,	0,	0},
   {"Pocket Monsters - Fire Red (Japan)",					"BPRJ",	131072,	0,	0,	0,	0},
   {"Pocket Monsters - Leaf Green (Japan)",				"BPGJ",	131072,	0,	0,	0,	0},
   {"Pocket Monsters - Ruby (Japan)",					"AXVJ",	131072,	0,	1,	0,	0},
   {"Pocket Monsters - Sapphire (Japan)",					"AXPJ",	131072,	0,	1,	0,	0},
   {"Pokemon Mystery Dungeon - Red Rescue Team (USA, Australia)",		"B24E",	131072,	0,	0,	0,	0},
   {"Pokemon Mystery Dungeon - Red Rescue Team (En,Fr,De,Es,It)",		"B24P",	131072,	0,	0,	0,	0},
   {"Pokemon - Blattgruene Edition (Germany)",				"BPGD",	131072,	0,	0,	0,	0},
   {"Pokemon - Edicion Rubi (Spain)",					"AXVS",	131072,	0,	1,	0,	0},
   {"Pokemon - Edicion Esmeralda (Spain)",					"BPES",	131072,	0,	1,	0,	0},
   {"Pokemon - Edicion Rojo Fuego (Spain)",				"BPRS",	131072,	1,	0,	0,	0},
   {"Pokemon - Edicion Verde Hoja (Spain)",				"BPGS",	131072,	1,	0,	0,	0},
   {"Pokemon - Eidicion Zafiro (Spain)",					"AXPS",	131072,	0,	1,	0,	0},
   {"Pokemon - Emerald Version (USA, Europe)",				"BPEE",	131072,	0,	1,	0,	0},
   {"Pokemon - Feuerrote Edition (Germany)",				"BPRD",	131072,	0,	0,	0,	0},
   {"Pokemon - Fire Red Version (USA, Europe)",				"BPRE",	131072,	0,	0,	0,	0},
   {"Pokemon - Leaf Green Version (USA, Europe)",				"BPGE",	131072,	0,	0,	0,	0},
   {"Pokemon - Rubin Edition (Germany)",					"AXVD",	131072,	0,	1,	0,	0},
   {"Pokemon - Ruby Version (USA, Europe)",				"AXVE",	131072,	0,	1,	0,	0},
   {"Pokemon - Sapphire Version (USA, Europe)",				"AXPE",	131072,	0,	1,	0,	0},
   {"Pokemon - Saphir Edition (Germany)",					"AXPD",	131072,	0,	1,	0,	0},
   {"Pokemon - Smaragd Edition (Germany)",					"BPED",	131072,	0,	1,	0,	0},
   {"Pokemon - Version Emeraude (France)",					"BPEF",	131072,	0,	1,	0,	0},
   {"Pokemon - Version Rouge Feu (France)",				"BPRF",	131072,	0,	0,	0,	0},
   {"Pokemon - Version Rubis (France)",					"AXVF",	131072,	0,	1,	0,	0},
   {"Pokemon - Version Saphir (France)",					"AXPF",	131072,	0,	1,	0,	0},
   {"Pokemon - Version Vert Feuille (France)",				"BPGF",	131072,	0,	0,	0,	0},
   {"Pokemon - Versione Rubino (Italy)",					"AXVI",	131072,	0,	1,	0,	0},
   {"Pokemon - Versione Rosso Fuoco (Italy)",				"BPRI",	131072,	0,	0,	0,	0},
   {"Pokemon - Versione Smeraldo (Italy)",					"BPEI",	131072,	0,	1,	0,	0},
   {"Pokemon - Versione Verde Foglia (Italy)",				"BPGI",	131072,	0,	0,	0,	0},
   {"Pokemon - Versione Zaffiro (Italy)",					"AXPI",	131072,	0,	1,	0,	0},
   {"Rockman EXE 4.5 - Real Operation (Japan)",				"BR4J",	0,	0,	1,	0,	0},
   {"Rocky (Europe)(En,Fr,De,Es,It)",					"AROP",	0,	1,	0,	0,	0},
   {"Rocky (USA)(En,Fr,De,Es,It)",						"AR8e",	0,	1,	0,	0,	0},
   {"Sennen Kazoku (Japan)",						"BKAJ",	131072,	0,	1,	0,	0},
   {"Shin Bokura no Taiyou - Gyakushuu no Sabata (Japan)",			"U33J",	0,	1,	1,	0,	0},
   {"Super Mario Advance 4 (Japan)",					"AX4J",	131072,	0,	0,	0,	0},
   {"Super Mario Advance 4 - Super Mario Bros. 3 (Europe)(En,Fr,De,Es,It)","AX4P",	131072,	0,	0,	0,	0},
   {"Super Mario Advance 4 - Super Mario Bros 3 - Super Mario Advance 4 v1.1 (USA)","AX4E",131072,0,0,0,0},
   {"Top Gun - Combat Zones (USA)(En,Fr,De,Es,It)",			"A2YE",	0,	5,	0,	0,	0},
   {"Yoshi's Universal Gravitation (Europe)(En,Fr,De,Es,It)",		"KYGP",	0,	4,	0,	0,	0},
   {"Yoshi no Banyuuinryoku (Japan)",					"KYGJ",	0,	4,	0,	0,	0},
   {"Yoshi - Topsy-Turvy (USA)",						"KYGE",	0,	1,	0,	0,	0},
   {"Yu-Gi-Oh! GX - Duel Academy (USA)",					"BYGE",	0,	2,	0,	0,	1},
   {"Yu-Gi-Oh! - Ultimate Masters - 2006 (Europe)(En,Jp,Fr,De,Es,It)",	"BY6P",	0,	2,	0,	0,	0},
   {"Zoku Bokura no Taiyou - Taiyou Shounen Django (Japan)",		"U32J",	0,	0,	1,	0,	0}
};

uint8 cpuBitsSet[256];
uint8 cpuLowestBitSet[256];

static bool CPUInit(const std::string bios_fn)
{
 FILE *memfp;
 char buffer[5];

 buffer[0] = rom[0xac];
 buffer[1] = rom[0xad];
 buffer[2] = rom[0xae];
 buffer[3] = rom[0xaf];
 buffer[4] = 0;

 FlashSizeSet = false;

 cpuSramEnabled = true;
 cpuFlashEnabled = true;
 cpuEEPROMEnabled = true;
 cpuEEPROMSensorEnabled = true;

 memfp = fopen(MDFN_MakeFName(MDFNMKF_SAV, 0, "type").c_str(), "rb");

 MDFN_printf("GameID:    %s\n", buffer);

 if(memfp)
 {
  char linebuffer[256];

  cpuSramEnabled = false;
  cpuFlashEnabled = false;
  cpuEEPROMEnabled = false;
  cpuEEPROMSensorEnabled = false;

  while(fgets(linebuffer, 256, memfp))
  {
   char args[2][256];
   int acount = sscanf(linebuffer, "%255s %255s", args[0], args[1]);

   if(acount < 1)
    continue;

   MDFN_printf(_("Backup memory type override: %s %s\n"), args[0], (acount > 1) ? args[1] : "");

   if(!strcasecmp(args[0], "sram"))
   {
    cpuSramEnabled = true;
   }
   else if(!strcasecmp(args[0], "flash"))
   {
    cpuFlashEnabled = true;
    if(acount == 2)
    {
     int size_temp = atoi(args[1]);

     if(size_temp == 0x10000 || size_temp == 0x20000)
     {
      flashSetSize(size_temp);
      FlashSizeSet = true;
     }
     else if(size_temp == 64 || size_temp == 128)
     {
      flashSetSize(size_temp * 1024);
      FlashSizeSet = true;
     }
     else
      puts("Flash size error");
    }
   }
   else if(!strcasecmp(args[0], "eeprom"))
    cpuEEPROMEnabled = true;
   else if(!strcasecmp(args[0], "sensor"))
    cpuEEPROMSensorEnabled = true;
   else if(!strcasecmp(args[0], "rtc"))
    GBA_RTC = new RTC();
  }
  fclose(memfp);
 }
 else
 {
  for(int i = 0; i < 256; i++)
  {
   if(!strcmp(gbaover[i].romid, buffer))
   {
    MDFN_printf("Found ROM in override list.\n");

    bool enableRTC = gbaover[i].rtcEnabled;
    if (enableRTC)
    {
     MDFN_printf("RTC:       enabled\n");
     GBA_RTC = new RTC();
    }

    int size_temp = gbaover[i].flashSize;
    if(size_temp != 0)
     size_temp = gbaover[i].flashSize;
    else
     size_temp = 65536;

    MDFN_printf("flashSize: %u\n", size_temp);

    if (size_temp == 0x10000 || size_temp == 0x20000)
    {
      flashSetSize(size_temp);
      FlashSizeSet = true;
    }

    bool mirroring = gbaover[i].mirroringEnabled;
    doMirroring(mirroring);

    int cpuSaveType = gbaover[i].saveType;
    switch(cpuSaveType) {
    default: // automatic
      cpuSramEnabled = true;
      cpuFlashEnabled = true;
      cpuEEPROMEnabled = true;
      cpuEEPROMSensorEnabled = true;
      MDFN_printf("Save type: auto\n");
      break;
    case 1: // EEPROM
      cpuSramEnabled = false;
      cpuFlashEnabled = false;
      cpuEEPROMEnabled = true;
      cpuEEPROMSensorEnabled = false;
      // EEPROM usage is automatically detected
      MDFN_printf("Save type: eeprom\n");
      break;
    case 2: // SRAM
      cpuSramEnabled = true;
      cpuFlashEnabled = false;
      cpuEEPROMEnabled = false;
      cpuEEPROMSensorEnabled = false;
      MDFN_printf("Save type: sram\n");
      break;
    case 3: // FLASH
      cpuSramEnabled = false;
      cpuFlashEnabled = true;
      cpuEEPROMEnabled = false;
      cpuEEPROMSensorEnabled = false;
      MDFN_printf("Save type: Flash\n");
      break;
    case 4: // EEPROM+Sensor
      cpuSramEnabled = false;
      cpuFlashEnabled = false;
      cpuEEPROMEnabled = true;
      cpuEEPROMSensorEnabled = true;
      MDFN_printf("Save type: Eeprom + sensor\n");
      break;
    case 5: // NONE
      cpuSramEnabled = false;
      cpuFlashEnabled = false;
      cpuEEPROMEnabled = false;
      cpuEEPROMSensorEnabled = false;
      MDFN_printf("Save type: none\n");
      break;
    }

    break;
   }
  }
 }

 // Detect hardware types
 hardware = SENSOR_NONE;
 if (buffer[0] == 'R') // Warioware Twisted (cartridge with rumble and z-axis gyro sensor)
  hardware = SENSOR_RUMBLE | SENSOR_GYRO;
 else if (buffer[0] == 'U') // Boktai 1 and 2 (cartridge with RTC and solar sensor)
  hardware = SENSOR_SOLAR;
 else if (buffer[0] == 'V')
  hardware = SENSOR_RUMBLE; // Drill Dozer (cartridge with rumble)

 if (hardware != SENSOR_NONE && GBA_RTC == NULL)
  GBA_RTC = new RTC(); // gpio pins is in RTC module

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

  MDFNFILE *bios_fp = file_open(MDFN_MakeFName(MDFNMKF_FIRMWARE, 0, bios_fn.c_str()).c_str());

  if(bios_fp)
  {
   if(GET_FSIZE_PTR(bios_fp) == 0x4000)
   {
    memcpy(bios, GET_FDATA_PTR(bios_fp), 0x4000);
    useBios = true;
   }
   else
    MDFN_printf("Invalid BIOS file size.\n");
   file_close(bios_fp);
  }
  else
   MDFN_printf("Cannot find GBA bios file. Using high-level bios emulation.\n");
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

  EEPROM_Reset();
  Flash_Reset();

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

void SetInput(unsigned port, const char *type, void *ptr)
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

void Emulate(EmulateSpecStruct *espec)
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

void DoSimpleCommand(int cmd)
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
