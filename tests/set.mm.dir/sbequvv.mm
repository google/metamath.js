include "weq.mm";
include "wsb.mm";
include "sbequivv.mm";
include "wi.mm";
include "equcoms.mm";
include "impbid.mm";

theorem sbequvv(wph: wff ph, vx: setvar x, vy: setvar y, vz: setvar z) {

  disjoint x z;
  disjoint y z;



  do {
    vx;
    vy;
    weq;
    wph;
    vz;
    vx;
    wsb;
    #;
    wph;
    vz;
    vy;
    wsb;
    #;
    wph;
    vx;
    vy;
    vz;
    sbequivv;
    @1;
    @0;
    wi;
    vy;
    vx;
    wph;
    vy;
    vx;
    vz;
    sbequivv;
    equcoms;
    impbid;
  };

  return |- "( x = y -> ( [ x / z ] ph <-> [ y / z ] ph ) )";
}
