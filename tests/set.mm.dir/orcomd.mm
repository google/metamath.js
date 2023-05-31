include "wo.mm";
include "orcom.mm";
include "sylib.mm";

theorem orcomd(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {
  assume orcomd.1: $|- ( ph -> ( ps \/ ch ) )$;





  do {
    wph;
    wps;
    wch;
    wo;
    wch;
    wps;
    wo;
    orcomd.1;
    wps;
    wch;
    orcom;
    sylib;
  };

  return $|-$ $( ph -> ( ch \/ ps ) )$;
}
