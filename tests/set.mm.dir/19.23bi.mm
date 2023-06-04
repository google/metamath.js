include "wex.mm";
include "19.8a.mm";
include "syl.mm";

theorem 19.23bi(wph: 'wff' ph, wps: 'wff' ps, vx: 'setvar' x) {
  assume 19.23bi.1: |- "( E. x ph -> ps )";





  do {
    wph;
    wph;
    vx;
    wex;
    wps;
    wph;
    vx;
    19.8a;
    19.23bi.1;
    syl;
  };

  return '|-' "( ph -> ps )";
}
