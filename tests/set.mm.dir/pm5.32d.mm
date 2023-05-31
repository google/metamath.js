include "wb.mm";
include "wi.mm";
include "wa.mm";
include "pm5.32.mm";
include "sylib.mm";

theorem pm5.32d(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th) {
  assume pm5.32d.1: $|- ( ph -> ( ps -> ( ch <-> th ) ) )$;





  do {
    wph;
    wps;
    wch;
    wth;
    wb;
    wi;
    wps;
    wch;
    wa;
    wps;
    wth;
    wa;
    wb;
    pm5.32d.1;
    wps;
    wch;
    wth;
    pm5.32;
    sylib;
  };

  return $|-$ $( ph -> ( ( ps /\ ch ) <-> ( ps /\ th ) ) )$;
}
