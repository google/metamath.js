include "wb.mm";
include "bicom1.mm";
include "ax-mp.mm";

theorem bicomi(wph: $wff$ ph, wps: $wff$ ps) {
  assume bicomi.1: $|- ( ph <-> ps )$;





  do {
    wph;
    wps;
    wb;
    wps;
    wph;
    wb;
    bicomi.1;
    wph;
    wps;
    bicom1;
    ax-mp;
  };

  return $|-$ $( ps <-> ph )$;
}
