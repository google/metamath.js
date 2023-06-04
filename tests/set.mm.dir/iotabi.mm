include "wb.mm";
include "wal.mm";
include "cab.mm";
include "cv.mm";
include "csn.mm";
include "wceq.mm";
include "cuni.mm";
include "cio.mm";
include "abbi.mm";
include "biimpi.mm";
include "eqeq1d.mm";
include "abbidv.mm";
include "unieqd.mm";
include "df-iota.mm";
include "3eqtr4g.mm";

theorem iotabi(wph: 'wff' ph, wps: 'wff' ps, vx: 'setvar' x) {



  let vz: setvar z;
  let vy: setvar y;

  do {
    wph;
    wps;
    wb;
    vx;
    wal;
    #;
    wph;
    vx;
    cab;
    #;
    vz;
    cv;
    csn;
    #;
    wceq;
    #;
    vz;
    cab;
    #;
    cuni;
    wps;
    vx;
    cab;
    #;
    @2;
    wceq;
    #;
    vz;
    cab;
    #;
    cuni;
    wph;
    vx;
    cio;
    wps;
    vx;
    cio;
    @0;
    @4;
    @7;
    @0;
    @3;
    @6;
    vz;
    @0;
    @1;
    @5;
    @2;
    @0;
    @1;
    @5;
    wceq;
    wph;
    wps;
    vx;
    abbi;
    biimpi;
    eqeq1d;
    abbidv;
    unieqd;
    wph;
    vx;
    vz;
    df-iota;
    wps;
    vx;
    vz;
    df-iota;
    3eqtr4g;
  };

  return '|-' "( A. x ( ph <-> ps ) -> ( iota x ph ) = ( iota x ps ) )";
}
