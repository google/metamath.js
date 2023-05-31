include "ex.mm";
include "com12.mm";

theorem expcom(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {
  assume ex.1: $|- ( ( ph /\ ps ) -> ch )$;





  do {
    wph;
    wps;
    wch;
    wph;
    wps;
    wch;
    ex.1;
    ex;
    com12;
  };

  return $|-$ $( ps -> ( ph -> ch ) )$;
}
