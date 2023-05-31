include "wo.mm";
include "orcd.mm";
include "olcd.mm";
include "jaoi.mm";

theorem orim12i(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th) {
  assume orim12i.1: $|- ( ph -> ps )$;
  assume orim12i.2: $|- ( ch -> th )$;





  do {
    wph;
    wps;
    wth;
    wo;
    wch;
    wph;
    wps;
    wth;
    orim12i.1;
    orcd;
    wch;
    wth;
    wps;
    orim12i.2;
    olcd;
    jaoi;
  };

  return $|-$ $( ( ph \/ ch ) -> ( ps \/ th ) )$;
}
