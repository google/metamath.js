include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cab.mm"
include "wcel.mm"
include "carden2b.mm"
include "com.mm"
include "1onn.mm"
include "cardnn.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "eqeq2i.mm"
include "biimpri.mm"
include "cdm.mm"
include "wb.mm"
include "c0.mm"
include "1n0.mm"
include "neii.mm"
include "eqeq1.mm"
include "mtbiri.mm"
include "ndmfv.mm"
include "nsyl2.mm"
include "con0.mm"
include "1on.mm"
include "onenon.mm"
include "carden2.mm"
include "sylancl.mm"
include "mpbid.mm"
include "impbii.mm"
include "cvv.mm"
include "elex.mm"
include "syl.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elab3.mm"
include "bitr4i.mm"

theorem pm54.43lem
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A ~~ 1o <-> A e. { x | ( card ` x ) = 1o } )

  proof
    cA
    c1o
    cen
    wbr
    #
    cA
    ccrd
    cfv
    #
    c1o
    wceq
    #
    cA
    vx
    cv
    #
    ccrd
    cfv
    #
    c1o
    wceq
    #
    vx
    cab
    wcel
    @0
    @2
    @0
    @1
    c1o
    ccrd
    cfv
    #
    c1o
    cA
    c1o
    carden2b
    c1o
    com
    wcel
    @6
    c1o
    wceq
    1onn
    c1o
    cardnn
    ax-mp
    #
    syl6eq
    @2
    @1
    @6
    wceq
    #
    @0
    @8
    @2
    @6
    c1o
    @1
    @7
    eqeq2i
    biimpri
    @2
    cA
    ccrd
    cdm
    #
    wcel
    #
    c1o
    @9
    wcel
    #
    @8
    @0
    wb
    @2
    @1
    c0
    wceq
    #
    @10
    @2
    @12
    c1o
    c0
    wceq
    c1o
    c0
    1n0
    neii
    @1
    c1o
    c0
    eqeq1
    mtbiri
    cA
    ccrd
    ndmfv
    nsyl2
    #
    c1o
    con0
    wcel
    @11
    1on
    c1o
    onenon
    ax-mp
    cA
    c1o
    carden2
    sylancl
    mpbid
    impbii
    @5
    @2
    vx
    cA
    @2
    @10
    cA
    cvv
    wcel
    @13
    cA
    @9
    elex
    syl
    @3
    cA
    wceq
    @4
    @1
    c1o
    @3
    cA
    ccrd
    fveq2
    eqeq1d
    elab3
    bitr4i
end
