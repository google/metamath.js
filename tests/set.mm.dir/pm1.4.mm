include "wo.mm";
include "olc.mm";
include "orc.mm";
include "jaoi.mm";

theorem pm1.4(wph: $wff$ ph, wps: $wff$ ps) {





  do {
    wph;
    wps;
    wph;
    wo;
    wps;
    wph;
    wps;
    olc;
    wps;
    wph;
    orc;
    jaoi;
  };

  return $|-$ $( ( ph \/ ps ) -> ( ps \/ ph ) )$;
}
