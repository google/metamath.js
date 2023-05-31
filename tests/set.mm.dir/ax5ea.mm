include "wex.mm";
include "wal.mm";
include "ax5e.mm";
include "ax-5.mm";
include "syl.mm";

theorem ax5ea(wph: $wff$ ph, vx: $setvar$ x) {

  disjoint ph x;



  do {
    wph;
    vx;
    wex;
    wph;
    wph;
    vx;
    wal;
    wph;
    vx;
    ax5e;
    wph;
    vx;
    ax-5;
    syl;
  };

  return $|-$ $( E. x ph -> A. x ph )$;
}
