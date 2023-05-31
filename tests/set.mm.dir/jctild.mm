include "a1d.mm";
include "jcad.mm";

theorem jctild(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th) {
  assume jctild.1: $|- ( ph -> ( ps -> ch ) )$;
  assume jctild.2: $|- ( ph -> th )$;





  do {
    wph;
    wps;
    wth;
    wch;
    wph;
    wth;
    wps;
    jctild.2;
    a1d;
    jctild.1;
    jcad;
  };

  return $|-$ $( ph -> ( ps -> ( th /\ ch ) ) )$;
}
