include "wi.mm";
include "wb.mm";
include "wn.mm";
include "df-bi.mm";
include "simprim.mm";
include "ax-mp.mm";
include "expi.mm";

theorem impbi(wph: $wff$ ph, wps: $wff$ ps) {





  do {
    wph;
    wps;
    wi;
    #;
    wps;
    wph;
    wi;
    #;
    wph;
    wps;
    wb;
    #;
    @2;
    @0;
    @1;
    wn;
    wi;
    wn;
    #;
    wi;
    #;
    @3;
    @2;
    wi;
    #;
    wn;
    wi;
    wn;
    @5;
    wph;
    wps;
    df-bi;
    @4;
    @5;
    simprim;
    ax-mp;
    expi;
  };

  return $|-$ $( ( ph -> ps ) -> ( ( ps -> ph ) -> ( ph <-> ps ) ) )$;
}
