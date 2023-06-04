include "wa.mm";
include "simpl.mm";
include "eximi.mm";

theorem exsimpl(wph: 'wff' ph, wps: 'wff' ps, vx: 'setvar' x) {





  do {
    wph;
    wps;
    wa;
    wph;
    vx;
    wph;
    wps;
    simpl;
    eximi;
  };

  return '|-' "( E. x ( ph /\\ ps ) -> E. x ph )";
}
