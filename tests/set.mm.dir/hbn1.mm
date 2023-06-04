include "ax-10.mm";

theorem hbn1(wph: 'wff' ph, vx: 'setvar' x) {





  do {
    wph;
    vx;
    ax-10;
  };

  return '|-' "( -. A. x ph -> A. x -. A. x ph )";
}
