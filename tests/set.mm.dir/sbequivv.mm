include "weq.mm";
include "wi.mm";
include "wal.mm";
include "wsb.mm";
include "equeuclr.mm";
include "imim1d.mm";
include "alimdv.mm";
include "sb6.mm";
include "3imtr4g.mm";

theorem sbequivv(wph: wff ph, vx: setvar x, vy: setvar y, vz: setvar z) {

  disjoint x z;
  disjoint y z;



  do {
    vx;
    vy;
    weq;
    #;
    vz;
    vx;
    weq;
    #;
    wph;
    wi;
    #;
    vz;
    wal;
    vz;
    vy;
    weq;
    #;
    wph;
    wi;
    #;
    vz;
    wal;
    wph;
    vz;
    vx;
    wsb;
    wph;
    vz;
    vy;
    wsb;
    @0;
    @2;
    @4;
    vz;
    @0;
    @3;
    @1;
    wph;
    vx;
    vz;
    vy;
    equeuclr;
    imim1d;
    alimdv;
    wph;
    vz;
    vx;
    sb6;
    wph;
    vz;
    vy;
    sb6;
    3imtr4g;
  };

  return |- "( x = y -> ( [ x / z ] ph -> [ y / z ] ph ) )";
}
