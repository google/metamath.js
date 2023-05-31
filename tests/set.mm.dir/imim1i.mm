include "id.mm";
include "imim12i.mm";

theorem imim1i(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {
  assume imim1i.1: $|- ( ph -> ps )$;





  do {
    wph;
    wps;
    wch;
    wch;
    imim1i.1;
    wch;
    id;
    imim12i;
  };

  return $|-$ $( ( ps -> ch ) -> ( ph -> ch ) )$;
}
