include "wb.mm";
include "a1d.mm";
include "pm5.74d.mm";

theorem imbi2d(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th) {
  assume imbid.1: $|- ( ph -> ( ps <-> ch ) )$;





  do {
    wph;
    wth;
    wps;
    wch;
    wph;
    wps;
    wch;
    wb;
    wth;
    imbid.1;
    a1d;
    pm5.74d;
  };

  return $|-$ $( ph -> ( ( th -> ps ) <-> ( th -> ch ) ) )$;
}
