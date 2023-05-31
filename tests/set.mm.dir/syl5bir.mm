include "biimpri.mm";
include "syl5.mm";

theorem syl5bir(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th) {
  assume syl5bir.1: $|- ( ps <-> ph )$;
  assume syl5bir.2: $|- ( ch -> ( ps -> th ) )$;





  do {
    wph;
    wps;
    wch;
    wth;
    wps;
    wph;
    syl5bir.1;
    biimpri;
    syl5bir.2;
    syl5;
  };

  return $|-$ $( ch -> ( ph -> th ) )$;
}
