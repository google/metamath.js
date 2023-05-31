include "wa.mm";
include "id.mm";
include "syl2an.mm";

theorem anim12i(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th) {
  assume anim12i.1: $|- ( ph -> ps )$;
  assume anim12i.2: $|- ( ch -> th )$;





  do {
    wph;
    wps;
    wth;
    wps;
    wth;
    wa;
    #;
    wch;
    anim12i.1;
    anim12i.2;
    @0;
    id;
    syl2an;
  };

  return $|-$ $( ( ph /\ ch ) -> ( ps /\ th ) )$;
}
