include "wcel.mm";
include "cv.mm";
include "wceq.mm";
include "wa.mm";
include "wex.mm";
include "df-clel.mm";
include "nfv.mm";
include "nfcvd.mm";
include "nfeqd.mm";
include "nfcrd.mm";
include "nfand.mm";
include "nfexd.mm";
include "nfxfrd.mm";

theorem nfeld(wph: wff ph, vx: setvar x, cA: class A, cB: class B) {
  assume nfeqd.1: |- "( ph -> F/_ x A )";
  assume nfeqd.2: |- "( ph -> F/_ x B )";



  let vy: setvar y;

  do {
    cA;
    cB;
    wcel;
    vy;
    cv;
    #;
    cA;
    wceq;
    #;
    @0;
    cB;
    wcel;
    #;
    wa;
    #;
    vy;
    wex;
    wph;
    vx;
    vy;
    cA;
    cB;
    df-clel;
    wph;
    @3;
    vx;
    vy;
    wph;
    vy;
    nfv;
    wph;
    @1;
    @2;
    vx;
    wph;
    vx;
    @0;
    cA;
    wph;
    vx;
    @0;
    nfcvd;
    nfeqd.1;
    nfeqd;
    wph;
    vx;
    vy;
    cB;
    nfeqd.2;
    nfcrd;
    nfand;
    nfexd;
    nfxfrd;
  };

  return |- "( ph -> F/ x A e. B )";
}
