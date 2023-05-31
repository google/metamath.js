include "wn.mm";
include "wi.mm";
include "con4.mm";
include "ax-mp.mm";

theorem con4i(wph: $wff$ ph, wps: $wff$ ps) {
  assume con4i.1: $|- ( -. ph -> -. ps )$;





  do {
    wph;
    wn;
    wps;
    wn;
    wi;
    wps;
    wph;
    wi;
    con4i.1;
    wph;
    wps;
    con4;
    ax-mp;
  };

  return $|-$ $( ps -> ph )$;
}
