include "wa.mm";
include "anbi1d.mm";
include "anbi2d.mm";
include "bitrd.mm";

theorem anbi12d(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th, wta: $wff$ ta) {
  assume anbi12d.1: $|- ( ph -> ( ps <-> ch ) )$;
  assume anbi12d.2: $|- ( ph -> ( th <-> ta ) )$;





  do {
    wph;
    wps;
    wth;
    wa;
    wch;
    wth;
    wa;
    wch;
    wta;
    wa;
    wph;
    wps;
    wch;
    wth;
    anbi12d.1;
    anbi1d;
    wph;
    wth;
    wta;
    wch;
    anbi12d.2;
    anbi2d;
    bitrd;
  };

  return $|-$ $( ph -> ( ( ps /\ th ) <-> ( ch /\ ta ) ) )$;
}
