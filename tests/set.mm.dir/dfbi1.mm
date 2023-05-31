include "wb.mm";
include "wi.mm";
include "wn.mm";
include "df-bi.mm";
include "simplim.mm";
include "ax-mp.mm";
include "impbi.mm";
include "impi.mm";
include "impbii.mm";

theorem dfbi1(wph: $wff$ ph, wps: $wff$ ps) {





  do {
    wph;
    wps;
    wb;
    #;
    wph;
    wps;
    wi;
    #;
    wps;
    wph;
    wi;
    #;
    wn;
    wi;
    wn;
    #;
    @0;
    @3;
    wi;
    #;
    @3;
    @0;
    wi;
    wn;
    #;
    wi;
    wn;
    @4;
    wph;
    wps;
    df-bi;
    @4;
    @5;
    simplim;
    ax-mp;
    @1;
    @2;
    @0;
    wph;
    wps;
    impbi;
    impi;
    impbii;
  };

  return $|-$ $( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) )$;
}
