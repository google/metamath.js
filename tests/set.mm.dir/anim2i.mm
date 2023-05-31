include "id.mm";
include "anim12i.mm";

theorem anim2i(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {
  assume anim1i.1: $|- ( ph -> ps )$;





  do {
    wch;
    wch;
    wph;
    wps;
    wch;
    id;
    anim1i.1;
    anim12i;
  };

  return $|-$ $( ( ch /\ ph ) -> ( ch /\ ps ) )$;
}
