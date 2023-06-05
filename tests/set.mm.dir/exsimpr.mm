include "wa.mm";
include "simpr.mm";
include "eximi.mm";

theorem exsimpr(wph: wff ph, wps: wff ps, vx: setvar x) {





  do {
    wph;
    wps;
    wa;
    wps;
    vx;
    wph;
    wps;
    simpr;
    eximi;
  };

  return |- "( E. x ( ph /\\ ps ) -> E. x ps )";
}
