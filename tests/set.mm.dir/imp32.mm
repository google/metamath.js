include "wa.mm";
include "impd.mm";
include "imp.mm";

theorem imp32(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th) {
  assume imp31.1: $|- ( ph -> ( ps -> ( ch -> th ) ) )$;





  do {
    wph;
    wps;
    wch;
    wa;
    wth;
    wph;
    wps;
    wch;
    wth;
    imp31.1;
    impd;
    imp;
  };

  return $|-$ $( ( ph /\ ( ps /\ ch ) ) -> th )$;
}
