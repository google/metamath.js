include "wal.mm";
include "nf5ri.mm";
include "hbal.mm";
include "nf5i.mm";

theorem nfal(wph: wff ph, vx: setvar x, vy: setvar y) {
  assume nfal.1: |- "F/ x ph";





  do {
    wph;
    vy;
    wal;
    vx;
    wph;
    vx;
    vy;
    wph;
    vx;
    nfal.1;
    nf5ri;
    hbal;
    nf5i;
  };

  return |- "F/ x A. y ph";
}
