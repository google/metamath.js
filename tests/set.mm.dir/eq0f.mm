include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "wn.mm"
include "nfcv.mm"
include "cleqf.mm"
include "noel.mm"
include "nbn.mm"
include "albii.mm"
include "bitr4i.mm"

theorem eq0f
  let vx: setvar x
  let cA: class A
  assume eq0f.1: |- F/_ x A


  assert |- ( A = (/) <-> A. x -. x e. A )

  proof
    cA
    c0
    wceq
    vx
    cv
    #
    cA
    wcel
    #
    @0
    c0
    wcel
    #
    wb
    #
    vx
    wal
    @1
    wn
    #
    vx
    wal
    vx
    cA
    c0
    eq0f.1
    vx
    c0
    nfcv
    cleqf
    @4
    @3
    vx
    @2
    @1
    @0
    noel
    nbn
    albii
    bitr4i
end
