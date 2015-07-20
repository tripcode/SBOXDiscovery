//
// Brute-force search algorithm for Bitslice DES S-box functions with Nvidia Maxwell LOP3.LUT instructions
//
// Algorithm based on:
// Kwan, Matthew. "Reducing the Gate Count of Bitslice DES." IACR Cryptology ePrint Archive 2000 (2000): 51.
// with heavy modification and adaption to look-up table instructions.
//
//
// By DeepLearningJohnDoe, 2015/07/20
// Contact: deeplearningjohndoe [at] gmail.com
//

//This program is free software: you can redistribute it and/or modify
//it under the terms of the GNU General Public License as published by
//the Free Software Foundation, either version 3 of the License, or
//(at your option) any later version.

//This program is distributed in the hope that it will be useful,
//but WITHOUT ANY WARRANTY; without even the implied warranty of
//MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//GNU General Public License for more details.

//You should have received a copy of the GNU General Public License
//along with this program.  If not, see <http://www.gnu.org/licenses/>.

using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading;
using System.Threading.Tasks;

namespace SBOXDiscovery
{
    class Program
    {
        static ulong lut3(ulong x, ulong y, ulong z, byte m)
        {
            ulong r = 0;
            if ((m & 1) != 0) r |= ~x & ~y & ~z;
            if ((m & 2) != 0) r |= ~x & ~y & z;
            if ((m & 4) != 0) r |= ~x & y & ~z;
            if ((m & 8) != 0) r |= ~x & y & z;
            if ((m & 16) != 0) r |= x & ~y & ~z;
            if ((m & 32) != 0) r |= x & ~y & z;
            if ((m & 64) != 0) r |= x & y & ~z;
            if ((m & 128) != 0) r |= x & y & z;
            return r;
        }

        [ThreadStatic]
        static Random rand;

        //3F
        static bool luttablefast(ulong target, ulong mask, ulong x, ulong y, ulong z)
        {
            ulong b = 0, k;
            k = ~x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            return MaskEqual(target, b, mask);
        }

        //3
        static bool luttable(ulong target, ulong mask, ulong x, ulong y, ulong z, out byte table)
        {
            table = 0;
            byte tableset = 0;

            ulong xx, yy, zz;
            int temp;
            for (int i = 0; i < 64; ++i)
            {
                if ((mask & 1) == 1)
                {
                    xx = x & 1; yy = y & 1; zz = z & 1;
                    temp = (int)((xx << 2) + (yy << 1) + zz);
                    if ((tableset & (1 << temp)) == 0)
                    {
                        table |= (byte)((target & 1) << temp);
                        tableset |= (byte)(1 << temp);
                    }
                    else if ((table & (1 << temp)) != (byte)((target & 1) << temp)) return false;
                }
                target >>= 1; mask >>= 1; x >>= 1; y >>= 1; z >>= 1;
            }

            //randomize table
            if (tableset != 0xFF)
            {
                byte[] buffer = new byte[1];
                rand.NextBytes(buffer);
                table |= (byte)(~tableset & buffer[0]);
            }

            return true;
        }

        //5F
        static bool luttablefast(ulong target, ulong mask, ulong v, ulong w, ulong x, ulong y, ulong z)
        {
            ulong b = 0, k;
            k = ~v & ~w & ~x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~v & ~w & ~x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~v & ~w & ~x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~v & ~w & ~x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~v & ~w & x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~v & ~w & x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~v & ~w & x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~v & ~w & x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~v & w & ~x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~v & w & ~x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~v & w & ~x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~v & w & ~x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~v & w & x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~v & w & x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~v & w & x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~v & w & x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = v & ~w & ~x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = v & ~w & ~x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = v & ~w & ~x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = v & ~w & ~x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = v & ~w & x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = v & ~w & x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = v & ~w & x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = v & ~w & x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = v & w & ~x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = v & w & ~x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = v & w & ~x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = v & w & ~x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = v & w & x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = v & w & x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = v & w & x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = v & w & x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            return MaskEqual(target, b, mask);
        }

        //5
        static bool luttable(ulong target, ulong mask, ulong v, ulong w, ulong x, ulong y, ulong z)
        {
            uint table = 0;
            uint tableset = 0;

            ulong vv, ww, xx, yy, zz;
            int temp;
            for (int i = 0; i < 64; ++i)
            {
                if ((mask & 1) == 1)
                {
                    vv = v & 1; ww = w & 1; xx = x & 1; yy = y & 1; zz = z & 1;
                    temp = (int)((vv << 4) + (ww << 3) + (xx << 2) + (yy << 1) + zz);
                    if ((tableset & (1 << temp)) == 0)
                    {
                        table |= (uint)((target & 1) << temp);
                        tableset |= (uint)(1 << temp);
                    }
                    else if ((table & (1 << temp)) != (uint)((target & 1) << temp)) return false;
                }
                target >>= 1; mask >>= 1; v >>= 1; w >>= 1; x >>= 1; y >>= 1; z >>= 1;
            }

            ////We don't use the out table anyway.
            ////randomize table
            //if (tableset != 0xFFFFFFFF)
            //{
            //    byte[] buffer = new byte[4];
            //    rand.NextBytes(buffer);
            //    table |= (uint)(~tableset & BitConverter.ToUInt32(buffer, 0));
            //}

            return true;
        }

        //7F
        static bool luttablefast(ulong target, ulong mask, ulong t, ulong u, ulong v, ulong w, ulong x, ulong y, ulong z)
        {
            ulong b = 0, k;
            k = ~t & ~u & ~v & ~w & ~x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & ~v & ~w & ~x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & ~v & ~w & ~x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & ~v & ~w & ~x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & ~v & ~w & x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & ~v & ~w & x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & ~v & ~w & x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & ~v & ~w & x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & ~v & w & ~x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & ~v & w & ~x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & ~v & w & ~x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & ~v & w & ~x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & ~v & w & x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & ~v & w & x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & ~v & w & x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & ~v & w & x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & v & ~w & ~x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & v & ~w & ~x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & v & ~w & ~x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & v & ~w & ~x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & v & ~w & x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & v & ~w & x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & v & ~w & x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & v & ~w & x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & v & w & ~x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & v & w & ~x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & v & w & ~x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & v & w & ~x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & v & w & x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & v & w & x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & v & w & x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & ~u & v & w & x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & ~v & ~w & ~x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & ~v & ~w & ~x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & ~v & ~w & ~x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & ~v & ~w & ~x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & ~v & ~w & x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & ~v & ~w & x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & ~v & ~w & x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & ~v & ~w & x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & ~v & w & ~x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & ~v & w & ~x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & ~v & w & ~x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & ~v & w & ~x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & ~v & w & x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & ~v & w & x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & ~v & w & x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & ~v & w & x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & v & ~w & ~x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & v & ~w & ~x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & v & ~w & ~x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & v & ~w & ~x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & v & ~w & x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & v & ~w & x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & v & ~w & x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & v & ~w & x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & v & w & ~x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & v & w & ~x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & v & w & ~x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & v & w & ~x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & v & w & x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & v & w & x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & v & w & x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = ~t & u & v & w & x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & ~v & ~w & ~x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & ~v & ~w & ~x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & ~v & ~w & ~x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & ~v & ~w & ~x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & ~v & ~w & x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & ~v & ~w & x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & ~v & ~w & x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & ~v & ~w & x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & ~v & w & ~x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & ~v & w & ~x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & ~v & w & ~x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & ~v & w & ~x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & ~v & w & x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & ~v & w & x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & ~v & w & x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & ~v & w & x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & v & ~w & ~x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & v & ~w & ~x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & v & ~w & ~x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & v & ~w & ~x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & v & ~w & x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & v & ~w & x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & v & ~w & x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & v & ~w & x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & v & w & ~x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & v & w & ~x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & v & w & ~x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & v & w & ~x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & v & w & x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & v & w & x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & v & w & x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & ~u & v & w & x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & ~v & ~w & ~x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & ~v & ~w & ~x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & ~v & ~w & ~x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & ~v & ~w & ~x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & ~v & ~w & x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & ~v & ~w & x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & ~v & ~w & x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & ~v & ~w & x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & ~v & w & ~x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & ~v & w & ~x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & ~v & w & ~x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & ~v & w & ~x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & ~v & w & x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & ~v & w & x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & ~v & w & x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & ~v & w & x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & v & ~w & ~x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & v & ~w & ~x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & v & ~w & ~x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & v & ~w & ~x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & v & ~w & x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & v & ~w & x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & v & ~w & x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & v & ~w & x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & v & w & ~x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & v & w & ~x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & v & w & ~x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & v & w & ~x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & v & w & x & ~y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & v & w & x & ~y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & v & w & x & y & ~z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            k = t & u & v & w & x & y & z;
            if (MaskEqual(target & k, k, mask)) b |= k;
            else if (!MaskEqual(target & k, 0, mask)) return false;
            return MaskEqual(target, b, mask);
        }

        [ThreadStatic]
        static bool[] table;
        [ThreadStatic]
        static bool[] tableset;

        //7
        static bool luttable(ulong target, ulong mask, ulong t, ulong u, ulong v, ulong w, ulong x, ulong y, ulong z)
        {
            if (table == null) table = new bool[128];
            if (tableset == null) tableset = new bool[128];
            else for (int i = 0; i < 128; ++i) tableset[i] = false;

            ulong tt, uu, vv, ww, xx, yy, zz;
            int temp;
            for (int i = 0; i < 64; ++i)
            {
                if ((mask & 1) == 1)
                {
                    tt = t & 1; uu = u & 1; vv = v & 1; ww = w & 1; xx = x & 1; yy = y & 1; zz = z & 1;
                    temp = (int)((tt << 6) + (uu << 5) + (vv << 4) + (ww << 3) + (xx << 2) + (yy << 1) + zz);
                    if (!tableset[temp])
                    {
                        table[temp] = ((target & 1) == 1);
                        tableset[temp] = true;
                    }
                    else if (table[temp] != ((target & 1) == 1)) return false;
                }
                target >>= 1; mask >>= 1; t >>= 1; u >>= 1; v >>= 1; w >>= 1; x >>= 1; y >>= 1; z >>= 1;
            }

            //Randomize table, for when we need to output table

            return true;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        static bool MaskEqual(ulong a, ulong b, ulong mask)
        {
            return (a & mask) == (b & mask);
        }

        static ulong[] initial = new ulong[6] { 0x5555555555555555, 0x3333333333333333, 0x0F0F0F0F0F0F0F0F, 0x00FF00FF00FF00FF, 0x0000FFFF0000FFFF, 0x00000000FFFFFFFF };

        [ThreadStatic]
        static byte[] shfl;
        [ThreadStatic]
        static byte[] shfl2;

        [ThreadStatic]
        static ulong[] cache;
        [ThreadStatic]
        static bool[] cachefilled;
        [ThreadStatic]
        static ulong[] cache2;
        [ThreadStatic]
        static bool[] cachefilled2;

        static int Rec(ref List<ulong> circuit, int mingate, ulong target, ulong mask, int selbit, int[] perm, out ulong value)
        {
            value = 0;

            if (Console.KeyAvailable)
            {
                return int.MinValue;
            }

            int gate = 0, tg;
            int g, h, i, j, k, l, m;
            ulong temp, temp2, temp3;
            //Existing gate?
            for (i = 0; i < circuit.Count; ++i)
            {
                temp = circuit[i];
                if (MaskEqual(temp, target, mask))
                {
                    //++gate; //It's in the circuit!
                    value = temp;
                    return gate;
                }
            }
            //Not of an existing gate?
            for (i = 0; i < circuit.Count; ++i)
            {
                temp = ~circuit[i];
                if (MaskEqual(temp, target, mask))
                {
                    //circuit.Add(temp); //add it to lut of the above layer implicitly
                    //++gate; //add it to lut of the above layer implicitly
                    value = temp;
                    return gate;
                }
            }
            //Two gates combined?
            for (i = 0; i < circuit.Count; ++i)
            {
                for (j = i + 1; j < circuit.Count; ++j)
                {
                    temp = circuit[i] & circuit[j];
                    if (MaskEqual(temp, target, mask))
                    {
                        circuit.Add(temp);
                        ++gate;
                        value = temp;
                        return gate;
                    }
                    temp = circuit[i] | circuit[j];
                    if (MaskEqual(temp, target, mask))
                    {
                        circuit.Add(temp);
                        ++gate;
                        value = temp;
                        return gate;
                    }
                    temp = circuit[i] ^ circuit[j];
                    if (MaskEqual(temp, target, mask))
                    {
                        circuit.Add(temp);
                        ++gate;
                        value = temp;
                        return gate;
                    }
                }
            }
            //Three gates combined with LUT?
            byte ll, ll2, ll22;
            for (i = 0; i < circuit.Count; ++i)
            {
                for (j = i + 1; j < circuit.Count; ++j) //Should we allow repeat here?
                {
                    for (k = j + 1; k < circuit.Count; ++k) //Should we allow repeat here?
                    {
                        if (!luttablefast(target, mask, circuit[i], circuit[j], circuit[k])) continue;
                        if (!luttable(target, mask, circuit[i], circuit[j], circuit[k], out ll)) continue;
                        temp = lut3(circuit[i], circuit[j], circuit[k], ll);
                        if (MaskEqual(temp, target, mask))
                        {
                            circuit.Add(temp);
                            ++gate;
                            value = temp;
                            return gate;
                        }
                        else
                        {
                            Console.WriteLine("FUCK");
                            System.Environment.Exit(1);
                        }
                    }
                }
            }

            if (circuit.Count <= 3) goto skiphigher;
            //FIVE GATES - lut(lut(g,h,i),j,k)
            if (cache == null) cache = new ulong[255];
            if (cachefilled == null) cachefilled = new bool[255];
            for (g = 0; g < circuit.Count; ++g)
            {
                for (h = g; h < circuit.Count; ++h)
                {
                    for (i = h; i < circuit.Count; ++i)
                    {
                        for (ll2 = 0; ll2 < 255; ++ll2) cachefilled[ll2] = false;
                        for (j = 0; j < circuit.Count; ++j)
                        {
                            for (k = j; k < circuit.Count; ++k)
                            {
                                if (!luttablefast(target, mask, circuit[g], circuit[h], circuit[i], circuit[j], circuit[k])) continue;
                                for (ll2 = 0; ll2 < 255; ++ll2) shfl[ll2] = ll2;
                                shfl.Shuffle(rand);
                                for (ll2 = 0; ll2 < 255; ++ll2)
                                {
                                    if (!cachefilled[shfl[ll2]])
                                    {
                                        cache[shfl[ll2]] = lut3(circuit[g], circuit[h], circuit[i], shfl[ll2]);
                                        cachefilled[shfl[ll2]] = true;
                                    }
                                    temp2 = cache[shfl[ll2]];
                                    if (!luttablefast(target, mask, temp2, circuit[j], circuit[k])) continue;
                                    if (!luttable(target, mask, temp2, circuit[j], circuit[k], out ll)) continue;
                                    temp = lut3(temp2, circuit[j], circuit[k], ll);
                                    circuit.Add(temp2);
                                    circuit.Add(temp);
                                    gate += 2;
                                    value = temp;
                                    return gate;
                                }
                            }
                        }
                    }
                }
            }

            //SEVEN GATES - lut(lut(g,h,i),lut(j,k,l),m)
            if (cache2 == null) cache2 = new ulong[255];
            if (cachefilled2 == null) cachefilled2 = new bool[255];
            for (g = 0; g < circuit.Count; ++g)
            {
                for (h = g; h < circuit.Count; ++h)
                {
                    for (i = h; i < circuit.Count; ++i)
                    {
                        if (Console.KeyAvailable) return int.MinValue;
                        for (ll2 = 0; ll2 < 255; ++ll2) cachefilled[ll2] = false;
                        for (j = g; j < circuit.Count; ++j)
                        {
                            for (k = j; k < circuit.Count; ++k)
                            {
                                for (l = k; l < circuit.Count; ++l)
                                {
                                    for (ll22 = 0; ll22 < 255; ++ll22) cachefilled2[ll22] = false;
                                    for (m = 0; m < circuit.Count; ++m)
                                    {
                                        if (!luttablefast(target, mask, circuit[g], circuit[h], circuit[i], circuit[j], circuit[k], circuit[l], circuit[m])) continue;
                                        for (ll2 = 0; ll2 < 255; ++ll2) shfl[ll2] = ll2;
                                        shfl.Shuffle(rand);
                                        for (ll22 = 0; ll22 < 255; ++ll22) shfl2[ll22] = ll22;
                                        shfl2.Shuffle(rand);
                                        for (ll2 = 0; ll2 < 255; ++ll2)
                                        {
                                            if (!cachefilled[shfl[ll2]])
                                            {
                                                cache[shfl[ll2]] = lut3(circuit[g], circuit[h], circuit[i], shfl[ll2]);
                                                cachefilled[shfl[ll2]] = true;
                                            }
                                            temp2 = cache[shfl[ll2]];
                                            if (!luttablefast(target, mask, temp2, circuit[j], circuit[k], circuit[l], circuit[m])) continue;
                                            for (ll22 = 0; ll22 < 255; ++ll22) //TODO: shuffle this too
                                            {
                                                if (!cachefilled2[shfl2[ll22]])
                                                {
                                                    cache2[shfl2[ll22]] = lut3(circuit[j], circuit[k], circuit[l], shfl2[ll22]);
                                                    cachefilled2[shfl2[ll22]] = true;
                                                }
                                                temp3 = cache2[shfl2[ll22]];
                                                if (!luttablefast(target, mask, temp2, temp3, circuit[m])) continue;
                                                if (!luttable(target, mask, temp2, temp3, circuit[m], out ll)) continue;
                                                temp = lut3(temp2, temp3, circuit[m], ll);
                                                circuit.Add(temp2);
                                                circuit.Add(temp3);
                                                circuit.Add(temp);
                                                gate += 3;
                                                value = temp;
                                                return gate;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }


            skiphigher:

            //if (selbit == 6) return int.MinValue; // This shouldn't happen though.

            int mintg = int.MaxValue;
            List<ulong> mincircuit = new List<ulong>();
            ulong minvalue = 0;
            ulong v1, v2;
            List<ulong> circuit0;
            int nn = (1 << perm[selbit]);

            //TODO: the sequence of below needs to be randomized, really
            //1
            circuit0 = circuit.ConvertAll(p => p);
            tg = 0;
            tg += Rec(ref circuit, mingate, target, mask & initial[perm[selbit]], selbit + 1, perm, out v1);
            if (tg >= mingate || tg < 0) return int.MinValue;
            tg += Rec(ref circuit, mingate, target, mask & ~initial[perm[selbit]], selbit + 1, perm, out v2);
            if (tg >= mingate || tg < 0) return int.MinValue;
            if (tg < mintg)
            {
                mintg = tg;
                minvalue = v1 & initial[perm[selbit]] | v2 & ~initial[perm[selbit]];
                if ((minvalue & mask) != (target & mask))
                {
                    {
                        Console.WriteLine("FUCK");
                        System.Environment.Exit(1);
                    }
                }
                mincircuit = circuit.ConvertAll(p => p);
            }
            circuit = circuit0.ConvertAll(p => p);
            tg = 0;
            tg += Rec(ref circuit, mingate, target, mask & ~initial[perm[selbit]], selbit + 1, perm, out v2);
            if (tg >= mingate || tg < 0) return int.MinValue;
            tg += Rec(ref circuit, mingate, target, mask & initial[perm[selbit]], selbit + 1, perm, out v1);
            if (tg >= mingate || tg < 0) return int.MinValue;
            if (tg < mintg || tg == mintg && rand.NextDouble() > 1.0 / 6)
            {
                mintg = tg;
                minvalue = v1 & initial[perm[selbit]] | v2 & ~initial[perm[selbit]];
                if ((minvalue & mask) != (target & mask))
                {
                    {
                        Console.WriteLine("FUCK");
                        System.Environment.Exit(1);
                    }
                }
                mincircuit = circuit.ConvertAll(p => p);
            }
            //2
            circuit = circuit0.ConvertAll(p => p);
            tg = 0;
            tg += Rec(ref circuit, mingate, target ^ (target >> nn | target << (64 - nn)), mask & initial[perm[selbit]], selbit + 1, perm, out v1);
            if (tg >= mingate || tg < 0) return int.MinValue;
            tg += Rec(ref circuit, mingate, target & ~initial[perm[selbit]] | (target >> nn | target << (64 - nn)) & initial[perm[selbit]], mask, selbit + 1, perm, out v2);
            if (tg >= mingate || tg < 0) return int.MinValue;
            if (tg < mintg || tg == mintg && rand.NextDouble() > 1.0 / 5)
            {
                mintg = tg;
                minvalue = (v1 ^ v2) & initial[perm[selbit]] | v2 & ~initial[perm[selbit]];
                if ((minvalue & mask) != (target & mask))
                {
                    {
                        Console.WriteLine("FUCK");
                        System.Environment.Exit(1);
                    }
                }
                mincircuit = circuit.ConvertAll(p => p);
            }
            circuit = circuit0.ConvertAll(p => p);
            tg = 0;
            tg += Rec(ref circuit, mingate, target & ~initial[perm[selbit]] | (target >> nn | target << (64 - nn)) & initial[perm[selbit]], mask, selbit + 1, perm, out v2);
            if (tg >= mingate || tg < 0) return int.MinValue;
            tg += Rec(ref circuit, mingate, target ^ (target >> nn | target << (64 - nn)), mask & initial[perm[selbit]], selbit + 1, perm, out v1);
            if (tg >= mingate || tg < 0) return int.MinValue;
            if (tg < mintg || tg == mintg && rand.NextDouble() > 1.0 / 4)
            {
                mintg = tg;
                minvalue = (v1 ^ v2) & initial[perm[selbit]] | v2 & ~initial[perm[selbit]];
                if ((minvalue & mask) != (target & mask))
                {
                    {
                        Console.WriteLine("FUCK");
                        System.Environment.Exit(1);
                    }
                }
                mincircuit = circuit.ConvertAll(p => p);
            }
            //2.5
            circuit = circuit0.ConvertAll(p => p);
            tg = 0;
            tg += Rec(ref circuit, mingate, target ^ (target << nn | target >> (64 - nn)), mask & ~initial[perm[selbit]], selbit + 1, perm, out v1);
            if (tg >= mingate || tg < 0) return int.MinValue;
            tg += Rec(ref circuit, mingate, target & initial[perm[selbit]] | (target << nn | target >> (64 - nn)) & ~initial[perm[selbit]], mask, selbit + 1, perm, out v2);
            if (tg >= mingate || tg < 0) return int.MinValue;
            if (tg < mintg || tg == mintg && rand.NextDouble() > 1.0 / 3)
            {
                mintg = tg;
                minvalue = (v1 ^ v2) & ~initial[perm[selbit]] | v2 & initial[perm[selbit]];
                if ((minvalue & mask) != (target & mask))
                {
                    {
                        Console.WriteLine("FUCK");
                        System.Environment.Exit(1);
                    }
                }
                mincircuit = circuit.ConvertAll(p => p);
            }
            circuit = circuit0.ConvertAll(p => p);
            tg = 0;
            tg += Rec(ref circuit, mingate, target & initial[perm[selbit]] | (target << nn | target >> (64 - nn)) & ~initial[perm[selbit]], mask, selbit + 1, perm, out v2);
            if (tg >= mingate || tg < 0) return int.MinValue;
            tg += Rec(ref circuit, mingate, target ^ (target << nn | target >> (64 - nn)), mask & ~initial[perm[selbit]], selbit + 1, perm, out v1);
            if (tg >= mingate || tg < 0) return int.MinValue;
            if (tg < mintg || tg == mintg && rand.NextDouble() > 1.0 / 2)
            {
                mintg = tg;
                minvalue = (v1 ^ v2) & ~initial[perm[selbit]] | v2 & initial[perm[selbit]];
                if ((minvalue & mask) != (target & mask))
                {
                    {
                        Console.WriteLine("FUCK");
                        System.Environment.Exit(1);
                    }
                }
                mincircuit = circuit.ConvertAll(p => p);
            }

            //Console.WriteLine("sel");
            gate = mintg;
            circuit = mincircuit;
            ++gate;
            value = minvalue;
            circuit.Add(value);
            return gate;
        }

        static IEnumerable<IEnumerable<T>> GetPermutations<T>(IEnumerable<T> list, int length)
        {
            if (length == 1) return list.Select(t => new T[] { t });

            return GetPermutations(list, length - 1)
                .SelectMany(t => list.Where(e => !t.Contains(e)),
                    (t1, t2) => t1.Concat(new T[] { t2 }));
        }

        static void Main(string[] args)
        {
            Process.GetCurrentProcess().PriorityClass = ProcessPriorityClass.Idle;

            Console.WriteLine("Select a s-box function (1~8):");
            int nn = Convert.ToInt32(Console.ReadLine());
            Console.WriteLine("Mingate (zero=no limit):");
            int mingate = Convert.ToInt32(Console.ReadLine());
            if (mingate == 0) mingate = int.MaxValue - 10;
            Console.WriteLine("Mindepth (zero=no limit):");
            int mindepth = Convert.ToInt32(Console.ReadLine());
            if (mindepth == 0) mindepth = int.MaxValue;

            ulong[][] ss = new ulong[8][];
            for (int i = 0; i < 8; ++i) ss[i] = new ulong[4];

            //1
            ss[0][0] = 0x94D83B6C6B68D433;
            ss[0][1] = 0xD6E19C325CA9E295;
            ss[0][2] = 0xB96C2D166993B874;
            ss[0][3] = 0x37994A96529E962D;

            //2
            ss[1][0] = 0xA79458E3784BC639;
            ss[1][1] = 0x9A5664B96A95959A;
            ss[1][2] = 0x8C6969D39E531CAC;
            ss[1][3] = 0xB14EA965DC3287C3;

            //3
            ss[2][0] = 0xD6A925D2835676A9;
            ss[2][1] = 0x496966B9967A9925;
            ss[2][2] = 0x9A1F4DA12D1BD23C;
            ss[2][3] = 0x738C3C69C9629796;

            //4
            ss[3][0] = 0x56E9861E9586CA37;
            ss[3][1] = 0x9586CA37A91679E1;
            ss[3][2] = 0xD2946D9A4CA36B59;
            ss[3][3] = 0xB35C94A6D2946D9A;

            //5
            ss[4][0] = 0x361A9C67C16AD6B4;
            ss[4][1] = 0x5B96A439B8691DC6;
            ss[4][2] = 0x9D2E4969D3A49C63;
            ss[4][3] = 0x1A6C35F266299A5D;

            //6
            ss[5][0] = 0xCAC5659A942D9A67;
            ss[5][1] = 0x925E63E169A49C79;
            ss[5][2] = 0x16E94A97B946D2B4;
            ss[5][3] = 0x5963A3C61C3EE619;

            //7
            ss[6][0] = 0x1C69B2DCB1C64A79;
            ss[6][1] = 0x8E1671ECE96016B7;
            ss[6][2] = 0x38D696A56385639E;
            ss[6][3] = 0x6A65956A94E97A94;

            //8
            ss[7][0] = 0xA59E6C3138D696A5;
            ss[7][1] = 0xCB471CB234E9B34C;
            ss[7][2] = 0x693CD92659698E63;
            ss[7][3] = 0xC729695A919AE965;

            IEnumerable<IEnumerable<int>> _perminput = GetPermutations(Enumerable.Range(0, 6), 6);
            IEnumerable<IEnumerable<int>> _permoutput = GetPermutations(Enumerable.Range(0, 4), 4);
            var perminput = _perminput.ToList().ConvertAll(p => p.ToArray());
            var permoutput = _permoutput.ToList().ConvertAll(p => p.ToArray());

            if (rand == null) rand = new Random();
            perminput.Shuffle(rand);
            permoutput.Shuffle(rand);

            List<ulong> mincircuit = new List<ulong>();
            int[] minp = null, minq = null;
            int count = 0;
            int N = perminput.Count * permoutput.Count;

            DateTime now = DateTime.Now;

            //Serial phase
            var options = new ParallelOptions();
            options.MaxDegreeOfParallelism = Environment.ProcessorCount;
            Console.WriteLine(options.MaxDegreeOfParallelism);

            bool termination = false;

            int[] dummy = new int[options.MaxDegreeOfParallelism];
            Parallel.ForEach(dummy, options, (_i, state) =>
                {
                    if (shfl == null) shfl = new byte[255];
                    if (shfl2 == null) shfl2 = new byte[255];
                    if (rand == null) rand = new Random((new Random()).Next() + Thread.CurrentThread.ManagedThreadId * 1299833);
                    while (true)
                    {
                        int[] p = perminput[rand.Next(perminput.Count)];
                        int[] q = permoutput[rand.Next(permoutput.Count)];

                        if (Console.KeyAvailable)
                        {
                            termination = true;
                            break;
                        }
                        int gate = 0;
                        double percent;
                        List<ulong> circuit = new List<ulong>();
                        for (int i = 0; i < 6; ++i) circuit.Add(initial[i]);
                        ulong a;
                        gate += Rec(ref circuit, mingate, ss[nn - 1][q[0]], 0xFFFFFFFFFFFFFFFF, 0, p, out a);
                        if (gate > mingate + 0 || gate < 0) goto fastexit;
                        gate += Rec(ref circuit, mingate, ss[nn - 1][q[1]], 0xFFFFFFFFFFFFFFFF, 0, p, out a);
                        if (gate > mingate + 0 || gate < 0) goto fastexit;
                        gate += Rec(ref circuit, mingate, ss[nn - 1][q[2]], 0xFFFFFFFFFFFFFFFF, 0, p, out a);
                        if (gate > mingate + 0 || gate < 0) goto fastexit;
                        gate += Rec(ref circuit, mingate, ss[nn - 1][q[3]], 0xFFFFFFFFFFFFFFFF, 0, p, out a);
                        if (gate > mingate + 0 || gate < 0) goto fastexit;
                        //if (gate < mingate) mingate = gate; //This isn't needed, because else it would be into fastexit

                        //Assert it's a valid solution:
                        //1. Desired values exist
                        int e = 0;
                        for (int h = 6; h < circuit.Count; ++h)
                        {
                            for (int i = 0; i < 4; ++i)
                            {
                                if (circuit[h] == ss[nn - 1][i]) ++e;
                            }
                        }
                        if (e != 4)
                        {
                            Console.WriteLine("You dun goofed A.");
                            System.Environment.Exit(1);
                        }
                        //2. All later values can be combined from earlier values
                        //Also check max depth at this step
                        int[] deptharray = new int[circuit.Count];
                        for (int h = 6; h < circuit.Count; ++h)
                        {
                            int i, j, k;
                            bool found = false;
                            byte ll = 0;
                            for (i = 0; i < h; ++i)
                            {
                                for (j = i; j < h; ++j)
                                {
                                    for (k = j; k < h; ++k)
                                    {
                                        if (luttable(circuit[h], 0xFFFFFFFFFFFFFFFF, circuit[i], circuit[j], circuit[k], out ll))
                                        {
                                            found = true;
                                            deptharray[h] = Math.Max(deptharray[i], Math.Max(deptharray[j], deptharray[k])) + 1;
                                            goto foundone;
                                        }
                                    }
                                }
                            }
                            Console.WriteLine("You dun goofed B.");
                            System.Environment.Exit(1);
                        foundone:
                            continue;
                        }
                        int depth = deptharray.Max();
                        //if (depth > mindepth || depth == mindepth && gate >= mingate) goto fastexit; //Prioritize depth
                        if (gate == mingate && depth >= mindepth) goto fastexit; //Prioritize gate count

                        //Output circuit
                        OutputCircuit(circuit, ss, nn, gate, depth);

                        mindepth = depth;
                        mingate = gate; //This isn't Math.Min(mingate, gate); because when depth goes down, gate count are much harder to go down
                        mincircuit = circuit.ConvertAll(z => z);
                        minp = p;
                        minq = q;
                        ++count;
                        percent = ((double)(count * 100)) / N;
                        Console.Clear();
                        Console.WriteLine("s{0}", nn);
                        Console.WriteLine("{0}{1}{2}{3}{4}{5} - {6}{7}{8}{9} - gate: {10}/{11}[D{12}] - circuit: {13} - {14:0.00}%", p[0], p[1], p[2], p[3], p[4], p[5], q[0], q[1], q[2], q[3], gate, mingate, mindepth, circuit.Count, percent);
                        Console.WriteLine("Traversal time: {0}", TimeSpan.FromTicks((long)((DateTime.Now - now).Ticks / (percent / 100))));
                        continue;
                    fastexit:
                        ++count;
                        percent = ((double)(count * 100)) / N;
                        Console.Clear();
                        Console.WriteLine("s{0}", nn);
                        Console.WriteLine("{0}{1}{2}{3}{4}{5} - {6}{7}{8}{9} - Fast exit/{10}[D{11}] - {12:0.00}%", p[0], p[1], p[2], p[3], p[4], p[5], q[0], q[1], q[2], q[3], mingate, mindepth, percent);
                        Console.WriteLine("Traversal time: {0}", TimeSpan.FromTicks((long)((DateTime.Now - now).Ticks / (percent / 100))));
                        continue;
                    }
                    if (termination == true) state.Stop();
                });

            Console.WriteLine("s{0}", nn);
            Console.WriteLine("{0}{1}{2}{3}{4}{5} - {6}{7}{8}{9} - gate: {10}[D{11}]", minp[0], minp[1], minp[2], minp[3], minp[4], minp[5], minq[0], minq[1], minq[2], minq[3], mingate, mindepth);
            Console.WriteLine("Total time: {0}", (DateTime.Now - now));

            Console.ReadLine();
        }

        //TODO: simplify with xor,or,and etc.. might not be faster, though.
        //Output mincircuit
        static void OutputCircuit(List<ulong> circuit, ulong[][] ss, int nn, int gate, int depth)
        {
            StreamWriter sw = new StreamWriter("s" + nn + "-" + gate + "D" + depth + ".txt");

            for (int h = 6; h < circuit.Count; ++h)
            {
                int i, j, k;
                byte ll = 0;
                for (i = 0; i < h; ++i)
                {
                    for (j = i; j < h; ++j)
                    {
                        for (k = j; k < h; ++k)
                        {
                            if (luttable(circuit[h], 0xFFFFFFFFFFFFFFFF, circuit[i], circuit[j], circuit[k], out ll))
                            {
                                if (circuit[h] == ss[nn - 1][0]) sw.Write("LUT(x1,");
                                else if (circuit[h] == ss[nn - 1][1]) sw.Write("LUT(x2,");
                                else if (circuit[h] == ss[nn - 1][2]) sw.Write("LUT(x3,");
                                else if (circuit[h] == ss[nn - 1][3]) sw.Write("LUT(x4,");
                                else sw.Write("LUT(x{0:X16},", circuit[h]);

                                if (i < 6) sw.Write("a{0},", i + 1);
                                else if (circuit[i] == ss[nn - 1][0]) sw.Write("x1,");
                                else if (circuit[i] == ss[nn - 1][1]) sw.Write("x2,");
                                else if (circuit[i] == ss[nn - 1][2]) sw.Write("x3,");
                                else if (circuit[i] == ss[nn - 1][3]) sw.Write("x4,");
                                else sw.Write("x{0:X16},", circuit[i]);
                                if (j < 6) sw.Write("a{0},", j + 1);
                                else if (circuit[j] == ss[nn - 1][0]) sw.Write("x1,");
                                else if (circuit[j] == ss[nn - 1][1]) sw.Write("x2,");
                                else if (circuit[j] == ss[nn - 1][2]) sw.Write("x3,");
                                else if (circuit[j] == ss[nn - 1][3]) sw.Write("x4,");
                                else sw.Write("x{0:X16},", circuit[j]);
                                if (k < 6) sw.Write("a{0},", k + 1);
                                else if (circuit[k] == ss[nn - 1][0]) sw.Write("x1,");
                                else if (circuit[k] == ss[nn - 1][1]) sw.Write("x2,");
                                else if (circuit[k] == ss[nn - 1][2]) sw.Write("x3,");
                                else if (circuit[k] == ss[nn - 1][3]) sw.Write("x4,");
                                else sw.Write("x{0:X16},", circuit[k]);

                                sw.WriteLine("0x{0:X2})", ll);

                                goto foundone;
                            }
                        }
                    }
                }
                Console.WriteLine("You dun goofed C.");
                System.Environment.Exit(1);
            foundone:
                continue;
            }

            sw.Close();
        }
    }

    public static class ExtensionMethods
    {
        public static void Shuffle<T>(this IList<T> list, Random rng)
        {
            int n = list.Count;
            while (n > 1)
            {
                n--;
                int k = rng.Next(n + 1);
                T value = list[k];
                list[k] = list[n];
                list[n] = value;
            }
        }
    }
}
