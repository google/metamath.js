include "wi.mm";
include "a1d.mm";
include "syldd.mm";

theorem syl5d(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th, wta: $wff$ ta) {
  assume syl5d.1: $|- ( ph -> ( ps -> ch ) )$;
  assume syl5d.2: $|- ( ph -> ( th -> ( ch -> ta ) ) )$;





  do {
    wph;
    wth;
    wps;
    wch;
    wta;
    wph;
    wps;
    wch;
    wi;
    wth;
    syl5d.1;
    a1d;
    syl5d.2;
    syldd;
  };

  return $|-$ $( ph -> ( th -> ( ps -> ta ) ) )$;
}
