include "wb.mm";
include "wi.mm";
include "wn.mm";
include "dfbi1.mm";
include "simprim.mm";
include "sylbi.mm";

theorem biimpr(wph: wff ph, wps: wff ps) {





  do {
    wph;
    wps;
    wb;
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
    @1;
    wph;
    wps;
    dfbi1;
    @0;
    @1;
    simprim;
    sylbi;
  };

  return |- "( ( ph <-> ps ) -> ( ps -> ph ) )";
}
