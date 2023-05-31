include "expcom.mm";
include "mpan9.mm";

theorem sylan(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th) {
  assume sylan.1: $|- ( ph -> ps )$;
  assume sylan.2: $|- ( ( ps /\ ch ) -> th )$;





  do {
    wph;
    wps;
    wch;
    wth;
    sylan.1;
    wps;
    wch;
    wth;
    sylan.2;
    expcom;
    mpan9;
  };

  return $|-$ $( ( ph /\ ch ) -> th )$;
}
