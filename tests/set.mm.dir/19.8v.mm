include "ax-5.mm";
include "19.8w.mm";

theorem 19.8v(wph: wff ph, vx: setvar x) {

  disjoint ph x;



  do {
    wph;
    vx;
    wph;
    vx;
    ax-5;
    19.8w;
  };

  return |- "( ph -> E. x ph )";
}
