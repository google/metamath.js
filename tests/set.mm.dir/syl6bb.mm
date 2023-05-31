include "wb.mm";
include "a1i.mm";
include "bitrd.mm";

theorem syl6bb(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th) {
  assume syl6bb.1: $|- ( ph -> ( ps <-> ch ) )$;
  assume syl6bb.2: $|- ( ch <-> th )$;





  do {
    wph;
    wps;
    wch;
    wth;
    syl6bb.1;
    wch;
    wth;
    wb;
    wph;
    syl6bb.2;
    a1i;
    bitrd;
  };

  return $|-$ $( ph -> ( ps <-> th ) )$;
}
