include "sylan.mm";
include "sylan2.mm";

theorem syl2an(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th, wta: $wff$ ta) {
  assume syl2an.1: $|- ( ph -> ps )$;
  assume syl2an.2: $|- ( ta -> ch )$;
  assume syl2an.3: $|- ( ( ps /\ ch ) -> th )$;





  do {
    wta;
    wph;
    wch;
    wth;
    syl2an.2;
    wph;
    wps;
    wch;
    wth;
    syl2an.1;
    syl2an.3;
    sylan;
    sylan2;
  };

  return $|-$ $( ( ph /\ ta ) -> th )$;
}
