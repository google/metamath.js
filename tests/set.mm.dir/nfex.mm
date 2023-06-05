include "wex.mm";
include "wn.mm";
include "wal.mm";
include "df-ex.mm";
include "nfn.mm";
include "nfal.mm";
include "nfxfr.mm";

theorem nfex(wph: wff ph, vx: setvar x, vy: setvar y) {
  assume nfex.1: |- "F/ x ph";





  do {
    wph;
    vy;
    wex;
    wph;
    wn;
    #;
    vy;
    wal;
    #;
    wn;
    vx;
    wph;
    vy;
    df-ex;
    @1;
    vx;
    @0;
    vx;
    vy;
    wph;
    vx;
    nfex.1;
    nfn;
    nfal;
    nfn;
    nfxfr;
  };

  return |- "F/ x E. y ph";
}
