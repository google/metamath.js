include "biimpi.mm";
include "sylbi.mm";

theorem sylbb(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {
  assume sylbb.1: $|- ( ph <-> ps )$;
  assume sylbb.2: $|- ( ps <-> ch )$;





  do {
    wph;
    wps;
    wch;
    sylbb.1;
    wps;
    wch;
    sylbb.2;
    biimpi;
    sylbi;
  };

  return $|-$ $( ph -> ch )$;
}
