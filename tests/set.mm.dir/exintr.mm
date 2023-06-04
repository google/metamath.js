include "wi.mm";
include "wa.mm";
include "ancl.mm";
include "aleximi.mm";

theorem exintr(wph: 'wff' ph, wps: 'wff' ps, vx: 'setvar' x) {





  do {
    wph;
    wps;
    wi;
    wph;
    wph;
    wps;
    wa;
    vx;
    wph;
    wps;
    ancl;
    aleximi;
  };

  return '|-' "( A. x ( ph -> ps ) -> ( E. x ph -> E. x ( ph /\\ ps ) ) )";
}
