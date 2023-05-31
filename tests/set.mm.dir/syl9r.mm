include "wi.mm";
include "syl9.mm";
include "com12.mm";

theorem syl9r(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th, wta: $wff$ ta) {
  assume syl9r.1: $|- ( ph -> ( ps -> ch ) )$;
  assume syl9r.2: $|- ( th -> ( ch -> ta ) )$;





  do {
    wph;
    wth;
    wps;
    wta;
    wi;
    wph;
    wps;
    wch;
    wth;
    wta;
    syl9r.1;
    syl9r.2;
    syl9;
    com12;
  };

  return $|-$ $( th -> ( ph -> ( ps -> ta ) ) )$;
}
