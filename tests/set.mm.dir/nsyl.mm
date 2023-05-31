include "nsyl3.mm";
include "con2i.mm";

theorem nsyl(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {
  assume nsyl.1: $|- ( ph -> -. ps )$;
  assume nsyl.2: $|- ( ch -> ps )$;





  do {
    wch;
    wph;
    wph;
    wps;
    wch;
    nsyl.1;
    nsyl.2;
    nsyl3;
    con2i;
  };

  return $|-$ $( ph -> -. ch )$;
}
