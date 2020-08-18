// -*- C++ -*-
// VisualBoyAdvance - Nintendo Gameboy/GameboyAdvance (TM) emulator.
// Copyright (C) 1999-2003 Forgotten
// Copyright (C) 2004 Forgotten and the VBA development team

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

#ifndef VBA_RTC_H
#define VBA_RTC_H

class RTC
{
 public:

 RTC();
 ~RTC();

 void InitTime(void);

 uint16 Read(uint32 address);
 void Write(uint32 address, uint16 value);
 void Reset(void);

 void AddTime(int32 amount);

 int StateAction(StateMem *sm, int load, int data_only);

 private:

 enum RTCSTATE { IDLE, COMMAND, DATA, READDATA };

 uint8 byte0;
 uint8 select;
 uint8 enable;
 uint8 command;
 int dataLen;
 int bits;
 RTCSTATE state;
 uint8 data[12];

 uint32 ClockCounter;

 //
 //
 //
 void ClockSeconds(void);
 bool BCDInc(uint8 &V, uint8 thresh, uint8 reset_val = 0x00);

 uint8 sec;
 uint8 min;
 uint8 hour;
 uint8 wday;
 uint8 mday;
 uint8 mon;
 uint8 year;
 // reserved data for future expansion
 uint8 reserved[12];
 bool reserved2;
 uint32 reserved3;
};

#endif
