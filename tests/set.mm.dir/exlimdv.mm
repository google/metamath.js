include "wex.mm";
include "eximdv.mm";
include "ax5e.mm";
include "syl6.mm";

theorem exlimdv(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, vx: $setvar$ x) {
  assume exlimdv.1: $|- ( ph -> ( ps -> ch ) )$;

  disjoint ch x;
  disjoint ph x;



  do {
    wph;
    wps;
    vx;
    wex;
    wch;
    vx;
    wex;
    wch;
    wph;
    wps;
    wch;
    vx;
    exlimdv.1;
    eximdv;
    wch;
    vx;
    ax5e;
    syl6;
  };

  return $|-$ $( ph -> ( E. x ps -> ch ) )$;
}
