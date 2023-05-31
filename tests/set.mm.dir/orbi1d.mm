include "wo.mm";
include "orbi2d.mm";
include "orcom.mm";
include "3bitr4g.mm";

theorem orbi1d(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th) {
  assume bid.1: $|- ( ph -> ( ps <-> ch ) )$;





  do {
    wph;
    wth;
    wps;
    wo;
    wth;
    wch;
    wo;
    wps;
    wth;
    wo;
    wch;
    wth;
    wo;
    wph;
    wps;
    wch;
    wth;
    bid.1;
    orbi2d;
    wps;
    wth;
    orcom;
    wch;
    wth;
    orcom;
    3bitr4g;
  };

  return $|-$ $( ph -> ( ( ps \/ th ) <-> ( ch \/ th ) ) )$;
}
