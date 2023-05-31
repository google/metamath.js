include "biimpi.mm";
include "syl5.mm";

theorem syl5bi(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th) {
  assume syl5bi.1: $|- ( ph <-> ps )$;
  assume syl5bi.2: $|- ( ch -> ( ps -> th ) )$;





  do {
    wph;
    wps;
    wch;
    wth;
    wph;
    wps;
    syl5bi.1;
    biimpi;
    syl5bi.2;
    syl5;
  };

  return $|-$ $( ch -> ( ph -> th ) )$;
}
