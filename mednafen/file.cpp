/* Mednafen - Multi-system Emulator
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

#include "mednafen.h"
#include <string.h>
#include <streams/file_stream.h>
#include "file.h"

struct MDFNFILE *file_open(const char *path)
{
   int64_t size          = 0;
   const char        *ld = NULL;
   struct MDFNFILE *file = (struct MDFNFILE*)calloc(1, sizeof(*file));

   if (!file)
      return NULL;

   if (!filestream_read_file(path, (void**)&file->data, &size))
      goto error;

   ld         = (const char*)strrchr(path, '.');
   file->size = (int64_t)size;
   file->ext  = strdup(ld ? ld + 1 : "");

   return file;

error:
   if (file)
      free(file);
   return NULL;
}

int file_close(struct MDFNFILE *file)
{
   if (!file)
      return 0;

   if (file->ext)
      free(file->ext);
   file->ext = NULL;

   if (file->data)
      free(file->data);
   file->data = NULL;

   free(file);

   return 1;
}

static INLINE bool MDFN_DumpToFileReal(const char *filename, int compress, const std::vector<PtrLengthPair> &pearpairs)
{
   FILE *fp = fopen(filename, "wb");

   if (!fp)
      return 0;

   for(unsigned int i = 0; i < pearpairs.size(); i++)
   {
      const void *data = pearpairs[i].GetData();
      const uint64 length = pearpairs[i].GetLength();

      if (fwrite(data, 1, length, fp) != length)
      {
         fclose(fp);
         return 0;
      }
   }

   if (fclose(fp) == EOF)
      return 0;

   return 1;
}

bool MDFN_DumpToFile(const char *filename, int compress, const std::vector<PtrLengthPair> &pearpairs)
{
   return (MDFN_DumpToFileReal(filename, compress, pearpairs));
}

bool MDFN_DumpToFile(const char *filename, int compress, const void *data, uint64 length)
{
   std::vector<PtrLengthPair> tmp_pairs;
   tmp_pairs.push_back(PtrLengthPair(data, length));
   return (MDFN_DumpToFileReal(filename, compress, tmp_pairs));
}
