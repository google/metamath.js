include "wal.mm";
include "wex.mm";
include "19.2.mm";
include "syl.mm";

theorem 19.2d(wph: 'wff' ph, wps: 'wff' ps, vx: 'setvar' x) {
  assume 19.2d.1: |- "( ph -> A. x ps )";





  do {
    wph;
    wps;
    vx;
    wal;
    wps;
    vx;
    wex;
    19.2d.1;
    wps;
    vx;
    19.2;
    syl;
  };

  return '|-' "( ph -> E. x ps )";
}
