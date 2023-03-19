include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wal.mm"
include "wex.mm"
include "wceq.mm"
include "wb.mm"
include "nfcv.mm"
include "cleqf.mm"
include "noel.mm"
include "nbn.mm"
include "albii.mm"
include "bitr4i.mm"
include "necon3abii.mm"
include "df-ex.mm"

theorem n0fOLD
  let vx: setvar x
  let cA: class A
  assume eq0f.1: |- F/_ x A


  assert |- ( A =/= (/) <-> E. x x e. A )

  proof
    cA
    c0
    wne
    vx
    cv
    #
    cA
    wcel
    #
    wn
    #
    vx
    wal
    #
    wn
    @1
    vx
    wex
    @3
    cA
    c0
    cA
    c0
    wceq
    @1
    @0
    c0
    wcel
    #
    wb
    #
    vx
    wal
    @3
    vx
    cA
    c0
    eq0f.1
    vx
    c0
    nfcv
    cleqf
    @2
    @5
    vx
    @4
    @1
    @0
    noel
    nbn
    albii
    bitr4i
    necon3abii
    @1
    vx
    df-ex
    bitr4i
end
