include "19.2d.mm";

theorem 19.8w(wph: wff ph, vx: setvar x) {
  assume 19.8w.1: |- "( ph -> A. x ph )";





  do {
    wph;
    wph;
    vx;
    19.8w.1;
    19.2d;
  };

  return |- "( ph -> E. x ph )";
}
