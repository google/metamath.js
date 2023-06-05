include "nf5ri.mm";
include "alrimih.mm";

theorem alrimi(wph: wff ph, wps: wff ps, vx: setvar x) {
  assume alrimi.1: |- "F/ x ph";
  assume alrimi.2: |- "( ph -> ps )";





  do {
    wph;
    wps;
    vx;
    wph;
    vx;
    alrimi.1;
    nf5ri;
    alrimi.2;
    alrimih;
  };

  return |- "( ph -> A. x ps )";
}
