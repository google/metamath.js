include "wo.mm";
include "wn.mm";
include "wi.mm";
include "df-or.mm";
include "mpbir.mm";

theorem orri(wph: $wff$ ph, wps: $wff$ ps) {
  assume orri.1: $|- ( -. ph -> ps )$;





  do {
    wph;
    wps;
    wo;
    wph;
    wn;
    wps;
    wi;
    orri.1;
    wph;
    wps;
    df-or;
    mpbir;
  };

  return $|-$ $( ph \/ ps )$;
}
