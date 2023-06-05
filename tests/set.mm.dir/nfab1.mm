include "cab.mm";
include "nfsab1.mm";
include "nfci.mm";

theorem nfab1(wph: wff ph, vx: setvar x) {



  let vy: setvar y;
  let cA: class A;

  do {
    vx;
    vy;
    wph;
    vx;
    cab;
    wph;
    vx;
    vy;
    nfsab1;
    nfci;
  };

  return |- "F/_ x { x | ph }";
}
