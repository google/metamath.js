include "wi.mm";
include "imim2i.mm";
include "a2d.mm";

theorem imim3i(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th) {
  assume imim3i.1: $|- ( ph -> ( ps -> ch ) )$;





  do {
    wth;
    wph;
    wi;
    wth;
    wps;
    wch;
    wph;
    wps;
    wch;
    wi;
    wth;
    imim3i.1;
    imim2i;
    a2d;
  };

  return $|-$ $( ( th -> ph ) -> ( ( th -> ps ) -> ( th -> ch ) ) )$;
}
