include "wnf.mm";
include "wal.mm";
include "sp.mm";
include "nf5r.mm";
include "impbid2.mm";

theorem 19.3t(wph: wff ph, vx: setvar x) {





  do {
    wph;
    vx;
    wnf;
    wph;
    vx;
    wal;
    wph;
    wph;
    vx;
    sp;
    wph;
    vx;
    nf5r;
    impbid2;
  };

  return |- "( F/ x ph -> ( A. x ph <-> ph ) )";
}
