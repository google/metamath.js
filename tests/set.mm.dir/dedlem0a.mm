include "wa.mm";
include "wi.mm";
include "iba.mm";
include "wb.mm";
include "biimt.mm";
include "jarri.mm";
include "bitrd.mm";

theorem dedlem0a(wph: wff ph, wps: wff ps, wch: wff ch) {





  do {
    wph;
    wps;
    wps;
    wph;
    wa;
    #;
    wch;
    wph;
    wi;
    #;
    @0;
    wi;
    #;
    wph;
    wps;
    iba;
    wch;
    wph;
    @0;
    @2;
    wb;
    @1;
    @0;
    biimt;
    jarri;
    bitrd;
  };

  return |- "( ph -> ( ps <-> ( ( ch -> ph ) -> ( ps /\\ ph ) ) ) )";
}
