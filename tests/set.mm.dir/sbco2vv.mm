include "wsb.mm";
include "nfv.mm";
include "sbequvv.mm";
include "sbiev.mm";

theorem sbco2vv(wph: wff ph, vx: setvar x, vy: setvar y, vz: setvar z) {

  disjoint x y;
  disjoint x z;
  disjoint y z;
  disjoint ph z;



  do {
    wph;
    vx;
    vz;
    wsb;
    wph;
    vx;
    vy;
    wsb;
    #;
    vz;
    vy;
    @0;
    vz;
    nfv;
    wph;
    vz;
    vy;
    vx;
    sbequvv;
    sbiev;
  };

  return |- "( [ y / z ] [ z / x ] ph <-> [ y / x ] ph )";
}
