include "wi.mm";
include "a1i.mm";
include "impbid.mm";

theorem impbid1(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {
  assume impbid1.1: $|- ( ph -> ( ps -> ch ) )$;
  assume impbid1.2: $|- ( ch -> ps )$;





  do {
    wph;
    wps;
    wch;
    impbid1.1;
    wch;
    wps;
    wi;
    wph;
    impbid1.2;
    a1i;
    impbid;
  };

  return $|-$ $( ph -> ( ps <-> ch ) )$;
}
