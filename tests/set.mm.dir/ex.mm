include "wn.mm";
include "wi.mm";
include "wa.mm";
include "df-an.mm";
include "sylbir.mm";
include "expi.mm";

theorem ex(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume ex.1: |- "( ( ph /\\ ps ) -> ch )";





  do {
    wph;
    wps;
    wch;
    wph;
    wps;
    wn;
    wi;
    wn;
    wph;
    wps;
    wa;
    wch;
    wph;
    wps;
    df-an;
    ex.1;
    sylbir;
    expi;
  };

  return '|-' "( ph -> ( ps -> ch ) )";
}
