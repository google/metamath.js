include "ax-4.mm";

theorem alim(wph: 'wff' ph, wps: 'wff' ps, vx: 'setvar' x) {





  do {
    wph;
    wps;
    vx;
    ax-4;
  };

  return '|-' "( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) )";
}
