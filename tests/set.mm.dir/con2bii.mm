include "wn.mm";
include "bicomi.mm";
include "con1bii.mm";

theorem con2bii(wph: $wff$ ph, wps: $wff$ ps) {
  assume con2bii.1: $|- ( ph <-> -. ps )$;





  do {
    wph;
    wn;
    wps;
    wps;
    wph;
    wph;
    wps;
    wn;
    con2bii.1;
    bicomi;
    con1bii;
    bicomi;
  };

  return $|-$ $( ps <-> -. ph )$;
}
