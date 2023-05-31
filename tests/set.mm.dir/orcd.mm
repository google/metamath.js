include "wo.mm";
include "orc.mm";
include "syl.mm";

theorem orcd(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {
  assume orcd.1: $|- ( ph -> ps )$;





  do {
    wph;
    wps;
    wps;
    wch;
    wo;
    orcd.1;
    wps;
    wch;
    orc;
    syl;
  };

  return $|-$ $( ph -> ( ps \/ ch ) )$;
}
