include "wex.mm";
include "eximi.mm";
include "ax5e.mm";
include "syl.mm";

theorem exlimiv(wph: wff ph, wps: wff ps, vx: setvar x) {
  assume exlimiv.1: |- "( ph -> ps )";

  disjoint ps x;



  do {
    wph;
    vx;
    wex;
    wps;
    vx;
    wex;
    wps;
    wph;
    wps;
    vx;
    exlimiv.1;
    eximi;
    wps;
    vx;
    ax5e;
    syl;
  };

  return |- "( E. x ph -> ps )";
}
