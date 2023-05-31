include "con4d.mm";
include "impbid.mm";

theorem impcon4bid(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {
  assume impcon4bid.1: $|- ( ph -> ( ps -> ch ) )$;
  assume impcon4bid.2: $|- ( ph -> ( -. ps -> -. ch ) )$;





  do {
    wph;
    wps;
    wch;
    impcon4bid.1;
    wph;
    wps;
    wch;
    impcon4bid.2;
    con4d;
    impbid;
  };

  return $|-$ $( ph -> ( ps <-> ch ) )$;
}
