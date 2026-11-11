/* x5/zinflate.c — the X5 ORACLE driver (DECLARATIONS-DEFLATE.md, Addendum A2): zlib's inflate in RAW mode (windowBits -15).
   usage: zinflate IN OUT   -> writes the inflated bytes to OUT and prints ONE line on stdout:
            ACCEPT <nbytes>              iff inflate returned Z_STREAM_END (bytes after the final block are ignored)
            REJECT <rc> <msg>            otherwise (Z_BUF_ERROR = truncated input, Z_DATA_ERROR, any other code)
   The whole input is given at once; inflate is called until it returns anything but Z_OK. Built against the zlib release named
   in Addendum A2 only, from its own sources, never a system zlib. */
#include <stdio.h>
#include <stdlib.h>
#include "zlib.h"
int main(int argc, char **argv) {
  if (argc != 3) { fprintf(stderr, "usage: zinflate IN OUT\n"); return 2; }
  FILE *f = fopen(argv[1], "rb"); if (!f) { perror("in"); return 2; }
  fseek(f, 0, SEEK_END); long n = ftell(f); fseek(f, 0, SEEK_SET);
  unsigned char *in = malloc(n > 0 ? n : 1); if (n > 0 && fread(in, 1, n, f) != (size_t)n) { perror("read"); return 2; } fclose(f);
  FILE *o = fopen(argv[2], "wb"); if (!o) { perror("out"); return 2; }
  z_stream s = {0}; if (inflateInit2(&s, -15) != Z_OK) { fprintf(stderr, "init\n"); return 2; }
  s.next_in = in; s.avail_in = (uInt)n;
  unsigned char buf[65536]; long total = 0; int rc;
  do {
    s.next_out = buf; s.avail_out = sizeof buf;
    rc = inflate(&s, Z_NO_FLUSH);
    size_t got = sizeof buf - s.avail_out; fwrite(buf, 1, got, o); total += got;
  } while (rc == Z_OK);
  fclose(o);
  if (rc == Z_STREAM_END) printf("ACCEPT %ld\n", total);
  else printf("REJECT %d %s\n", rc, s.msg ? s.msg : "(no message)");
  inflateEnd(&s); return 0;
}
