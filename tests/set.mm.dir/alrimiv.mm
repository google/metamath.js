include "ax-5.mm";
include "alrimih.mm";

theorem alrimiv(wph: wff ph, wps: wff ps, vx: setvar x) {
  assume alrimiv.1: |- "( ph -> ps )";

  disjoint ph x;



  do {
    wph;
    wps;
    vx;
    wph;
    vx;
    ax-5;
    alrimiv.1;
    alrimih;
  };

  return |- "( ph -> A. x ps )";
}
