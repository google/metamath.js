include "idd.mm";
include "anim12d.mm";

theorem anim2d(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th) {
  assume anim1d.1: $|- ( ph -> ( ps -> ch ) )$;





  do {
    wph;
    wth;
    wth;
    wps;
    wch;
    wph;
    wth;
    idd;
    anim1d.1;
    anim12d;
  };

  return $|-$ $( ph -> ( ( th /\ ps ) -> ( th /\ ch ) ) )$;
}
