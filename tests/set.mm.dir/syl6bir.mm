include "biimprd.mm";
include "syl6.mm";

theorem syl6bir(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th) {
  assume syl6bir.1: $|- ( ph -> ( ch <-> ps ) )$;
  assume syl6bir.2: $|- ( ch -> th )$;





  do {
    wph;
    wps;
    wch;
    wth;
    wph;
    wch;
    wps;
    syl6bir.1;
    biimprd;
    syl6bir.2;
    syl6;
  };

  return $|-$ $( ph -> ( ps -> th ) )$;
}
