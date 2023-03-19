include "cvv.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "nfcv.mm"
include "cleqf.mm"
include "vex.mm"
include "tbt.mm"
include "albii.mm"
include "bitr4i.mm"

theorem eqvf
  let vx: setvar x
  let cA: class A
  assume eqvf.1: |- F/_ x A


  assert |- ( A = _V <-> A. x x e. A )

  proof
    cA
    cvv
    wceq
    vx
    cv
    #
    cA
    wcel
    #
    @0
    cvv
    wcel
    #
    wb
    #
    vx
    wal
    @1
    vx
    wal
    vx
    cA
    cvv
    eqvf.1
    vx
    cvv
    nfcv
    cleqf
    @1
    @3
    vx
    @2
    @1
    vx
    vex
    tbt
    albii
    bitr4i
end
