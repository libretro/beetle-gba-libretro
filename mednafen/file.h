#ifndef MDFN_FILE_H
#define MDFN_FILE_H

#include <string>

#define MDFNFILE_EC_NOTFOUND	1
#define MDFNFILE_EC_OTHER	2

struct MDFNFILE
{
 char    *ext;
 uint8_t *data;
 int64_t size;
 int64_t location;
};

struct MDFNFILE *file_open(const char *path);
int file_close(struct MDFNFILE *file);

class PtrLengthPair
{
 public:

 inline PtrLengthPair(const void *new_data, const uint64 new_length)
 {
  data = new_data;
  length = new_length;
 }

 ~PtrLengthPair() 
 { 

 } 

 INLINE const void *GetData(void) const
 {
  return(data);
 }

 INLINE uint64 GetLength(void) const
 {
  return(length);
 }

 private:
 const void *data;
 uint64 length;
};

#include <vector>

// These functions should be used for data like save states and non-volatile backup memory.
// Until(if, even) we add LoadFromFile functions, for reading the files these functions generate, just use gzopen(), gzread(), etc.
// "compress" is set to the zlib compression level.  0 disables compression entirely, and dumps the file without a gzip header or footer.
// (Note: There is a setting that will force compress to 0 in the internal DumpToFile logic, for hackers who don't want to ungzip save files.)

bool MDFN_DumpToFile(const char *filename, int compress, const void *data, const uint64 length);
bool MDFN_DumpToFile(const char *filename, int compress, const std::vector<PtrLengthPair> &pearpairs);

#endif
