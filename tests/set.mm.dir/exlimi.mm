include "wi.mm";
include "wex.mm";
include "19.23.mm";
include "mpgbi.mm";

theorem exlimi(wph: 'wff' ph, wps: 'wff' ps, vx: 'setvar' x) {
  assume exlimi.1: |- "F/ x ps";
  assume exlimi.2: |- "( ph -> ps )";





  do {
    wph;
    wps;
    wi;
    wph;
    vx;
    wex;
    wps;
    wi;
    vx;
    wph;
    wps;
    vx;
    exlimi.1;
    19.23;
    exlimi.2;
    mpgbi;
  };

  return '|-' "( E. x ph -> ps )";
}
