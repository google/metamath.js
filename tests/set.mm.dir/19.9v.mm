include "wex.mm";
include "ax5e.mm";
include "19.8v.mm";
include "impbii.mm";

theorem 19.9v(wph: $wff$ ph, vx: $setvar$ x) {

  disjoint ph x;



  do {
    wph;
    vx;
    wex;
    wph;
    wph;
    vx;
    ax5e;
    wph;
    vx;
    19.8v;
    impbii;
  };

  return $|-$ $( E. x ph <-> ph )$;
}
