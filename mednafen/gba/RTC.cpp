// Mednafen GBA Emulation Module(based on VisualBoyAdvance)
// Copyright (C) 1999-2003 Forgotten
// Copyright (C) 2005 Forgotten and the VBA development team
// Copyright (C) 2009-2017 Mednafen Team

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

#include "../mednafen.h"
#include "GBA.h"
#include "Globals.h"
#include "Port.h"

#include <time.h>

RTC::RTC()
{
 sec = 0x00;
 min = 0x00;
 hour = 0x00;
 wday = 0x00;
 mday = 0x01;
 mon = 0x01;
 year = 0x00;

 InitTime();
 Reset(); 
}

RTC::~RTC()
{

}

static uint8 toBCD(uint8 value)
{
  value = value % 100;
  int l = value % 10;
  int h = value / 10;
  return h * 16 + l;
}

void RTC::InitTime(void)
{
 struct tm *toom;
 time_t long_time;
 
 time( &long_time );                /* Get time as long integer. */
 toom = localtime( &long_time ); /* Convert to local time. */

 sec = toBCD(toom->tm_sec);
 min = toBCD(toom->tm_min);
 hour = toBCD(toom->tm_hour);
 wday = toBCD(toom->tm_wday);
 mday = toBCD(toom->tm_mday);
 mon = toBCD(toom->tm_mon + 1);
 year = toBCD(toom->tm_year % 100);

 if(sec >= 0x60)	// Murder the leap second.
  sec = 0x59;
}

bool RTC::BCDInc(uint8 &V, uint8 thresh, uint8 reset_val)
{
 V = ((V + 1) & 0x0F) | (V & 0xF0);
 if((V & 0x0F) >= 0x0A)
 {
  V &= 0xF0;
  V += 0x10;

  if((V & 0xF0) >= 0xA0)
  {
   V &= 0x0F;
  }
 }

 if(V >= thresh)
 {
  V = reset_val;

  return(true);
 }

 return(false);
}

void RTC::ClockSeconds(void)
{
 if(BCDInc(sec, 0x60))
 {
  if(BCDInc(min, 0x60))
  {
   if(BCDInc(hour, 0x24))
   {
    uint8 mday_thresh = 0x32;

    if(mon == 0x02)
    {
     mday_thresh = 0x29;

     if(((year & 0x0F) % 4) == ((year & 0x10) ? 0x02 : 0x00))
      mday_thresh = 0x30;
    }
    else if(mon == 0x04 || mon == 0x06 || mon == 0x09 || mon == 0x11)
     mday_thresh = 0x31;

    BCDInc(wday, 0x07);

    if(BCDInc(mday, mday_thresh, 0x01))
    {
     if(BCDInc(mon, 0x13, 0x01))
     {
      BCDInc(year, 0xA0);
     }
    }
   }
  }
 }
}


void RTC::AddTime(int32 amount)
{
 ClockCounter += amount;

 while(ClockCounter >= 16777216)
 {
  ClockCounter -= 16777216;
  ClockSeconds();
 }
}

uint16 RTC::Read(uint32 address)
{
  if (address == 0x80000c8)
    return enable;

  if (address == 0x80000c6)
    return select;

  if (address == 0x80000c4) {
    int ret = 0;

    if (!(enable & 1))
      return 0;

    // Boktai Solar Sensor
    if (select == 7) {
      if (reserved[11] >= systemGetSensorDarkness())
        ret |= 8;
    }

    // WarioWare Twisted Tilt Sensor
    if (select == 0x0b) {
      uint16 v = systemGetSensorZ() + 0x6C0;
      ret |= ((v >> reserved[11]) & 1) << 2;
    }

    // Real Time Clock
    if (select & 0x04)
      ret |= byte0;

    return ret;
  }

  return READ16LE(((uint16*)&rom[address & 0x1FFFFFE]));

 // abort();
}

void RTC::Write(uint32 address, uint16 value)
{
  if(address == 0x80000c8) {
    enable = (uint8)value; // enable ?
  } else if(address == 0x80000c6) {
    select = (uint8)value; // read/write
    // Rumble Off
    if (!(value & 8))
      systemCartridgeRumble(false);
  } else if(address == 0x80000c4) {
    // Rumble (Wario Twister, Drill Dozer)
    if (select & 8)
      systemCartridgeRumble(value & 8);

    // Boktai solar sensor
    if (select == 7) {
      if (value & 2) {
        // reset counter to 0
        reserved[11] = 0;
      }

      if ((value & 1) && (!(reserved[10] & 1))) {
        // increase counter, ready to do another read
        if (reserved[11] < 255)
          reserved[11]++;
        else
          reserved[11] = 0;
      }

      reserved[10] = value & select;
    }

    // WarioWare Twisted rotation sensor
    if (select == 0xb) {
      if (value & 2) {
        // clock goes high in preperation for reading a bit
        reserved[11]--;
      }

      if (value & 1) {
        // start ADC conversion
        reserved[11] = 15;
      }

      byte0 = value & select;
    }

    // Real Time Clock
    if(select & 1) {
      if(state == IDLE && byte0 == 1 && value == 5) {
          state = COMMAND;
          bits = 0;
          command = 0;
      } else if(!(byte0 & 1) && (value & 1)) { // bit transfer
        byte0 = (uint8)value;        
        switch(state) {
        case COMMAND:
          command |= ((value & 2) >> 1) << (7-bits);
          bits++;
          if(bits == 8) {
            bits = 0;
            switch(command) {
            case 0x60:
              // not sure what this command does but it doesn't take parameters
              // maybe it is a reset or stop
              state = IDLE;
              bits = 0;
              break;
            case 0x62:
              // this sets the control state but not sure what those values are
              state = READDATA;
              dataLen = 1;
              break;
            case 0x63:
              dataLen = 1;
              data[0] = 0x40;
              state = DATA;
              break;
           case 0x64:
              break;
            case 0x65:
              {                
                dataLen = 7;
                data[0] = year;
                data[1] = mon;
                data[2] = mday;
                data[3] = wday;
                data[4] = hour;
                data[5] = min;
                data[6] = sec;
                state = DATA;
              }
              break;              
            case 0x67:
              {
                dataLen = 3;
                data[0] = hour;
                data[1] = min;
                data[2] = sec;
                state = DATA;
              }
              break;
            default:
              //systemMessage(0, N_("Unknown RTC command %02x"), command);
              state = IDLE;
              break;
            }
          }
          break;
        case DATA:
          if(select & 2) {
          } else if(select & 4) {
            byte0 = (byte0 & ~2) |
              ((data[bits >> 3] >>
                (bits & 7)) & 1)*2;
            bits++;
            if(bits == 8*dataLen) {
              bits = 0;
              state = IDLE;
            }
          }
          break;
        case READDATA:
          if(!(select & 2)) {
          } else {
            data[bits >> 3] =
              (data[bits >> 3] >> 1) |
              ((value << 6) & 128);
            bits++;
            if(bits == 8*dataLen) {
              bits = 0;
              state = IDLE;
            }
          }
          break;
		default:
          break;
        }
      } else
        byte0 = (uint8)value;
    }
  }
}

void RTC::Reset(void)
{
 byte0 = 0;
 select = 0;
 enable = 0;
 command = 0;
 dataLen = 0;
 bits = 0;
 state = IDLE;

 memset(data, 0, sizeof(data));
 ClockCounter = 0;
 reserved[11] = 0;
}

int RTC::StateAction(StateMem *sm, int load, int data_only)
{
 SFORMAT StateRegs[] = 
 {
  SFVAR(byte0),
  SFVAR(select),
  SFVAR(enable),
  SFVAR(command),
  SFVAR(dataLen),
  SFVAR(bits),
  SFVAR(state),
  SFARRAY(data, 12),

  SFVAR(ClockCounter),

  SFVAR(sec),
  SFVAR(min),
  SFVAR(hour),
  SFVAR(wday),
  SFVAR(mday),
  SFVAR(mon),
  SFVAR(year),

  SFARRAY(reserved, 12),
  SFVAR(reserved2),
  SFVAR(reserved3),

  SFEND
 };


 int ret = MDFNSS_StateAction(sm, load, data_only, StateRegs, "RTC", false);

 if(load)
 {

 }

 return(ret);
}
