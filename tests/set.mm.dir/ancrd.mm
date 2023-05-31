include "idd.mm";
include "jcad.mm";

theorem ancrd(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {
  assume ancrd.1: $|- ( ph -> ( ps -> ch ) )$;





  do {
    wph;
    wps;
    wch;
    wps;
    ancrd.1;
    wph;
    wps;
    idd;
    jcad;
  };

  return $|-$ $( ph -> ( ps -> ( ch /\ ps ) ) )$;
}
