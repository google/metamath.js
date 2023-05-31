include "wa.mm";
include "pm3.2.mm";
include "syl6c.mm";

theorem jcad(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th) {
  assume jcad.1: $|- ( ph -> ( ps -> ch ) )$;
  assume jcad.2: $|- ( ph -> ( ps -> th ) )$;





  do {
    wph;
    wps;
    wch;
    wth;
    wch;
    wth;
    wa;
    jcad.1;
    jcad.2;
    wch;
    wth;
    pm3.2;
    syl6c;
  };

  return $|-$ $( ph -> ( ps -> ( ch /\ th ) ) )$;
}
