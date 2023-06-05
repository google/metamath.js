include "wceq.mm";
include "cv.mm";
include "wcel.mm";
include "wb.mm";
include "wal.mm";
include "dfcleq.mm";
include "nfv.mm";
include "nfcrd.mm";
include "nfbid.mm";
include "nfald.mm";
include "nfxfrd.mm";

theorem nfeqd(wph: wff ph, vx: setvar x, cA: class A, cB: class B) {
  assume nfeqd.1: |- "( ph -> F/_ x A )";
  assume nfeqd.2: |- "( ph -> F/_ x B )";



  let vy: setvar y;

  do {
    cA;
    cB;
    wceq;
    vy;
    cv;
    #;
    cA;
    wcel;
    #;
    @0;
    cB;
    wcel;
    #;
    wb;
    #;
    vy;
    wal;
    wph;
    vx;
    vy;
    cA;
    cB;
    dfcleq;
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
    vy;
    cA;
    nfeqd.1;
    nfcrd;
    wph;
    vx;
    vy;
    cB;
    nfeqd.2;
    nfcrd;
    nfbid;
    nfald;
    nfxfrd;
  };

  return |- "( ph -> F/ x A = B )";
}
