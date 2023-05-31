include "wb.mm";
include "biid.mm";
include "a1i.mm";

theorem biidd(wph: $wff$ ph, wps: $wff$ ps) {





  do {
    wps;
    wps;
    wb;
    wph;
    wps;
    biid;
    a1i;
  };

  return $|-$ $( ph -> ( ps <-> ps ) )$;
}
