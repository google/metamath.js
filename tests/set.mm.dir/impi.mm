include "wn.mm";
include "wi.mm";
include "con3rr3.mm";
include "con1i.mm";

theorem impi(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {
  assume impi.1: $|- ( ph -> ( ps -> ch ) )$;





  do {
    wch;
    wph;
    wps;
    wn;
    wi;
    wph;
    wps;
    wch;
    impi.1;
    con3rr3;
    con1i;
  };

  return $|-$ $( -. ( ph -> -. ps ) -> ch )$;
}
