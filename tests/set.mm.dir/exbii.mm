include "wb.mm";
include "wex.mm";
include "exbi.mm";
include "mpg.mm";

theorem exbii(wph: $wff$ ph, wps: $wff$ ps, vx: $setvar$ x) {
  assume exbii.1: $|- ( ph <-> ps )$;





  do {
    wph;
    wps;
    wb;
    wph;
    vx;
    wex;
    wps;
    vx;
    wex;
    wb;
    vx;
    wph;
    wps;
    vx;
    exbi;
    exbii.1;
    mpg;
  };

  return $|-$ $( E. x ph <-> E. x ps )$;
}
