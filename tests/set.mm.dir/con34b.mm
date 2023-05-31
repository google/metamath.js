include "wi.mm";
include "wn.mm";
include "con3.mm";
include "con4.mm";
include "impbii.mm";

theorem con34b(wph: $wff$ ph, wps: $wff$ ps) {





  do {
    wph;
    wps;
    wi;
    wps;
    wn;
    wph;
    wn;
    wi;
    wph;
    wps;
    con3;
    wps;
    wph;
    con4;
    impbii;
  };

  return $|-$ $( ( ph -> ps ) <-> ( -. ps -> -. ph ) )$;
}
