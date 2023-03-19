include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "con0.mm"
include "wcel.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "wss.mm"
include "wi.mm"
include "wral.mm"
include "cardon.mm"
include "eleq1.mm"
include "mpbii.mm"
include "crab.mm"
include "cint.mm"
include "wa.mm"
include "cardonle.mm"
include "biantrurd.mm"
include "eqss.mm"
include "syl6rbbr.mm"
include "oncardval.mm"
include "sseq2d.mm"
include "bitrd.mm"
include "ssint.mm"
include "breq1.mm"
include "elrab.mm"
include "ensymb.mm"
include "anbi2i.mm"
include "bitri.mm"
include "imbi1i.mm"
include "impexp.mm"
include "ralbii2.mm"
include "syl6bb.mm"
include "biadan2.mm"

theorem iscard2
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( ( card ` A ) = A <-> ( A e. On /\ A. x e. On ( A ~~ x -> A C_ x ) ) )

  proof
    cA
    ccrd
    cfv
    #
    cA
    wceq
    #
    cA
    con0
    wcel
    #
    cA
    vx
    cv
    #
    cen
    wbr
    #
    cA
    @3
    wss
    #
    wi
    #
    vx
    con0
    wral
    #
    @1
    @0
    con0
    wcel
    @2
    cA
    cardon
    @0
    cA
    con0
    eleq1
    mpbii
    @2
    @1
    cA
    vy
    cv
    #
    cA
    cen
    wbr
    #
    vy
    con0
    crab
    #
    cint
    #
    wss
    #
    @7
    @2
    @1
    cA
    @0
    wss
    #
    @12
    @2
    @13
    @0
    cA
    wss
    #
    @13
    wa
    @1
    @2
    @14
    @13
    cA
    cardonle
    biantrurd
    @0
    cA
    eqss
    syl6rbbr
    @2
    @0
    @11
    cA
    vy
    cA
    oncardval
    sseq2d
    bitrd
    @12
    @5
    vx
    @10
    wral
    @7
    vx
    cA
    @10
    ssint
    @5
    @6
    vx
    @10
    con0
    @3
    @10
    wcel
    #
    @5
    wi
    @3
    con0
    wcel
    #
    @4
    wa
    #
    @5
    wi
    @16
    @6
    wi
    @15
    @17
    @5
    @15
    @16
    @3
    cA
    cen
    wbr
    #
    wa
    @17
    @9
    @18
    vy
    @3
    con0
    @8
    @3
    cA
    cen
    breq1
    elrab
    @18
    @4
    @16
    @3
    cA
    ensymb
    anbi2i
    bitri
    imbi1i
    @16
    @4
    @5
    impexp
    bitri
    ralbii2
    bitri
    syl6bb
    biadan2
end
