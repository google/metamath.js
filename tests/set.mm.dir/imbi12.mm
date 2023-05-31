include "wb.mm";
include "wi.mm";
include "wn.mm";
include "simplim.mm";
include "simprim.mm";
include "imbi12d.mm";
include "expi.mm";

theorem imbi12(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th) {





  do {
    wph;
    wps;
    wb;
    #;
    wch;
    wth;
    wb;
    #;
    wph;
    wch;
    wi;
    wps;
    wth;
    wi;
    wb;
    @0;
    @1;
    wn;
    #;
    wi;
    wn;
    wph;
    wps;
    wch;
    wth;
    @0;
    @2;
    simplim;
    @0;
    @1;
    simprim;
    imbi12d;
    expi;
  };

  return $|-$ $( ( ph <-> ps ) -> ( ( ch <-> th ) -> ( ( ph -> ch ) <-> ( ps -> th ) ) ) )$;
}
