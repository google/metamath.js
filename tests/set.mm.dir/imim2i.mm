include "wi.mm";
include "a1i.mm";
include "a2i.mm";

theorem imim2i(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {
  assume imim2i.1: $|- ( ph -> ps )$;





  do {
    wch;
    wph;
    wps;
    wph;
    wps;
    wi;
    wch;
    imim2i.1;
    a1i;
    a2i;
  };

  return $|-$ $( ( ch -> ph ) -> ( ch -> ps ) )$;
}
