include "wa.mm";
include "expcom.mm";
include "adantrd.mm";
include "mpcom.mm";

theorem syldan(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th) {
  assume syldan.1: $|- ( ( ph /\ ps ) -> ch )$;
  assume syldan.2: $|- ( ( ph /\ ch ) -> th )$;





  do {
    wch;
    wph;
    wps;
    wa;
    wth;
    syldan.1;
    wch;
    wph;
    wth;
    wps;
    wph;
    wch;
    wth;
    syldan.2;
    expcom;
    adantrd;
    mpcom;
  };

  return $|-$ $( ( ph /\ ps ) -> th )$;
}
