include "wi.mm";
include "id.mm";
include "exgen.mm";
include "19.35i.mm";

theorem 19.2(wph: 'wff' ph, vx: 'setvar' x) {





  do {
    wph;
    wph;
    vx;
    wph;
    wph;
    wi;
    vx;
    wph;
    id;
    exgen;
    19.35i;
  };

  return '|-' "( A. x ph -> E. x ph )";
}
