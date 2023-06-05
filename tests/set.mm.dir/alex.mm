include "wal.mm";
include "wn.mm";
include "wex.mm";
include "notnotb.mm";
include "albii.mm";
include "alnex.mm";
include "bitri.mm";

theorem alex(wph: wff ph, vx: setvar x) {





  do {
    wph;
    vx;
    wal;
    wph;
    wn;
    #;
    wn;
    #;
    vx;
    wal;
    @0;
    vx;
    wex;
    wn;
    wph;
    @1;
    vx;
    wph;
    notnotb;
    albii;
    @0;
    vx;
    alnex;
    bitri;
  };

  return |- "( A. x ph <-> -. E. x -. ph )";
}
