include "wal.mm";
include "sp.mm";
include "syl.mm";

theorem sps(wph: 'wff' ph, wps: 'wff' ps, vx: 'setvar' x) {
  assume sps.1: |- "( ph -> ps )";





  do {
    wph;
    vx;
    wal;
    wph;
    wps;
    wph;
    vx;
    sp;
    sps.1;
    syl;
  };

  return '|-' "( A. x ph -> ps )";
}
