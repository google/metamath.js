include "wa.mm";
include "wn.mm";
include "wi.mm";
include "df-an.mm";
include "con2bii.mm";

theorem imnan(wph: 'wff' ph, wps: 'wff' ps) {





  do {
    wph;
    wps;
    wa;
    wph;
    wps;
    wn;
    wi;
    wph;
    wps;
    df-an;
    con2bii;
  };

  return '|-' "( ( ph -> -. ps ) <-> -. ( ph /\\ ps ) )";
}
