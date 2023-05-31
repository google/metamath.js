include "syl5.mm";
include "impcom.mm";

theorem mpan9(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th) {
  assume mpan9.1: $|- ( ph -> ps )$;
  assume mpan9.2: $|- ( ch -> ( ps -> th ) )$;





  do {
    wch;
    wph;
    wth;
    wph;
    wps;
    wch;
    wth;
    mpan9.1;
    mpan9.2;
    syl5;
    impcom;
  };

  return $|-$ $( ( ph /\ ch ) -> th )$;
}
