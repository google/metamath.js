include "wi.mm";
include "wn.mm";
include "wa.mm";
include "iman.mm";
include "con2bii.mm";

theorem annim(wph: 'wff' ph, wps: 'wff' ps) {





  do {
    wph;
    wps;
    wi;
    wph;
    wps;
    wn;
    wa;
    wph;
    wps;
    iman;
    con2bii;
  };

  return '|-' "( ( ph /\\ -. ps ) <-> -. ( ph -> ps ) )";
}
