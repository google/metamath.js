include "a1d.mm";
include "sylcom.mm";

theorem syl5com(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th) {
  assume syl5com.1: $|- ( ph -> ps )$;
  assume syl5com.2: $|- ( ch -> ( ps -> th ) )$;





  do {
    wph;
    wch;
    wps;
    wth;
    wph;
    wps;
    wch;
    syl5com.1;
    a1d;
    syl5com.2;
    sylcom;
  };

  return $|-$ $( ph -> ( ch -> th ) )$;
}
