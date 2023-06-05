include "wal.mm";
include "nfri.mm";
include "19.23bi.mm";

theorem nf5ri(wph: wff ph, vx: setvar x) {
  assume nf5ri.1: |- "F/ x ph";





  do {
    wph;
    wph;
    vx;
    wal;
    vx;
    wph;
    vx;
    nf5ri.1;
    nfri;
    19.23bi;
  };

  return |- "( ph -> A. x ph )";
}
