include "wa.mm";
include "wn.mm";
include "wi.mm";
include "df-an.mm";
include "impi.mm";
include "sylbi.mm";

theorem imp(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {
  assume imp.1: $|- ( ph -> ( ps -> ch ) )$;





  do {
    wph;
    wps;
    wa;
    wph;
    wps;
    wn;
    wi;
    wn;
    wch;
    wph;
    wps;
    df-an;
    wph;
    wps;
    wch;
    imp.1;
    impi;
    sylbi;
  };

  return $|-$ $( ( ph /\ ps ) -> ch )$;
}
