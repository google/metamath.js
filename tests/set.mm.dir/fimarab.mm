include "wf.mm"
include "wss.mm"
include "wa.mm"
include "cima.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "crab.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "wcel.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "fvelimab.mm"
include "anbi2d.mm"
include "sylan.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "syl5ss.mm"
include "adantr.mm"
include "sseld.mm"
include "pm4.71rd.mm"
include "rabid.mm"
include "a1i.mm"
include "3bitr4d.mm"
include "eqrd.mm"

theorem fimarab
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X

  disjoint A y
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint x y
  disjoint X x
  disjoint X y
  assert |- ( ( F : A --> B /\ X C_ A ) -> ( F " X ) = { y e. B | E. x e. X ( F ` x ) = y } )

  proof
    cA
    cB
    cF
    wf
    #
    cX
    cA
    wss
    #
    wa
    #
    vy
    cF
    cX
    cima
    #
    vx
    cv
    cF
    cfv
    vy
    cv
    #
    wceq
    vx
    cX
    wrex
    #
    vy
    cB
    crab
    #
    @2
    vy
    nfv
    vy
    @3
    nfcv
    @5
    vy
    cB
    nfrab1
    @2
    @4
    cB
    wcel
    #
    @4
    @3
    wcel
    #
    wa
    #
    @7
    @5
    wa
    #
    @8
    @4
    @6
    wcel
    #
    @0
    cF
    cA
    wfn
    #
    @1
    @9
    @10
    wb
    cA
    cB
    cF
    ffn
    @12
    @1
    wa
    @8
    @5
    @7
    vx
    cA
    cX
    @4
    cF
    fvelimab
    anbi2d
    sylan
    @2
    @8
    @7
    @2
    @3
    cB
    @4
    @0
    @3
    cB
    wss
    @1
    @0
    @3
    cF
    crn
    cB
    cF
    cX
    imassrn
    cA
    cB
    cF
    frn
    syl5ss
    adantr
    sseld
    pm4.71rd
    @11
    @10
    wb
    @2
    @5
    vy
    cB
    rabid
    a1i
    3bitr4d
    eqrd
end
