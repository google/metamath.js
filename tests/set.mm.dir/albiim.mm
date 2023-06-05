include "wb.mm";
include "wal.mm";
include "wi.mm";
include "wa.mm";
include "dfbi2.mm";
include "albii.mm";
include "19.26.mm";
include "bitri.mm";

theorem albiim(wph: wff ph, wps: wff ps, vx: setvar x) {





  do {
    wph;
    wps;
    wb;
    #;
    vx;
    wal;
    wph;
    wps;
    wi;
    #;
    wps;
    wph;
    wi;
    #;
    wa;
    #;
    vx;
    wal;
    @1;
    vx;
    wal;
    @2;
    vx;
    wal;
    wa;
    @0;
    @3;
    vx;
    wph;
    wps;
    dfbi2;
    albii;
    @1;
    @2;
    vx;
    19.26;
    bitri;
  };

  return |- "( A. x ( ph <-> ps ) <-> ( A. x ( ph -> ps ) /\\ A. x ( ps -> ph ) ) )";
}
