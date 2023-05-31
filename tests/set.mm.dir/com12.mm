include "id.mm";
include "syl5com.mm";

theorem com12(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {
  assume com12.1: $|- ( ph -> ( ps -> ch ) )$;





  do {
    wps;
    wps;
    wph;
    wch;
    wps;
    id;
    com12.1;
    syl5com;
  };

  return $|-$ $( ps -> ( ph -> ch ) )$;
}
