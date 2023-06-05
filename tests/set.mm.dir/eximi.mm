include "wi.mm";
include "wex.mm";
include "exim.mm";
include "mpg.mm";

theorem eximi(wph: wff ph, wps: wff ps, vx: setvar x) {
  assume eximi.1: |- "( ph -> ps )";





  do {
    wph;
    wps;
    wi;
    wph;
    vx;
    wex;
    wps;
    vx;
    wex;
    wi;
    vx;
    wph;
    wps;
    vx;
    exim;
    eximi.1;
    mpg;
  };

  return |- "( E. x ph -> E. x ps )";
}
