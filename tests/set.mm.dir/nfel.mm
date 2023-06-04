include "wcel.mm";
include "wnf.mm";
include "wtru.mm";
include "wnfc.mm";
include "a1i.mm";
include "nfeld.mm";
include "mptru.mm";

theorem nfel(vx: 'setvar' x, cA: 'class' A, cB: 'class' B) {
  assume nfnfc.1: |- "F/_ x A";
  assume nfeq.2: |- "F/_ x B";



  let vz: setvar z;
  let vy: setvar y;

  do {
    cA;
    cB;
    wcel;
    vx;
    wnf;
    wtru;
    vx;
    cA;
    cB;
    vx;
    cA;
    wnfc;
    wtru;
    nfnfc.1;
    a1i;
    vx;
    cB;
    wnfc;
    wtru;
    nfeq.2;
    a1i;
    nfeld;
    mptru;
  };

  return '|-' "F/ x A e. B";
}
