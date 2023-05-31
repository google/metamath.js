include "wb.mm";
include "a1i.mm";
include "pm5.32ri.mm";

theorem anbi1i(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {
  assume anbi.1: $|- ( ph <-> ps )$;





  do {
    wch;
    wph;
    wps;
    wph;
    wps;
    wb;
    wch;
    anbi.1;
    a1i;
    pm5.32ri;
  };

  return $|-$ $( ( ph /\ ch ) <-> ( ps /\ ch ) )$;
}
