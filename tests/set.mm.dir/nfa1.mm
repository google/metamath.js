include "wal.mm";
include "wn.mm";
include "wex.mm";
include "alex.mm";
include "nfe1.mm";
include "nfn.mm";
include "nfxfr.mm";

theorem nfa1(wph: wff ph, vx: setvar x) {





  do {
    wph;
    vx;
    wal;
    wph;
    wn;
    #;
    vx;
    wex;
    #;
    wn;
    vx;
    wph;
    vx;
    alex;
    @1;
    vx;
    @0;
    vx;
    nfe1;
    nfn;
    nfxfr;
  };

  return |- "F/ x A. x ph";
}
