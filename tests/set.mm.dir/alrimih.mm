include "sylg.mm";

theorem alrimih(wph: 'wff' ph, wps: 'wff' ps, vx: 'setvar' x) {
  assume alrimih.1: |- "( ph -> A. x ph )";
  assume alrimih.2: |- "( ph -> ps )";





  do {
    wph;
    wph;
    wps;
    vx;
    alrimih.1;
    alrimih.2;
    sylg;
  };

  return '|-' "( ph -> A. x ps )";
}
