include "wfn.mm"
include "wss.mm"
include "w3a.mm"
include "cun.mm"
include "cima.mm"
include "cv.mm"
include "wcel.mm"
include "wo.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "simp1.mm"
include "wa.mm"
include "simpl.mm"
include "simpr.mm"
include "unssd.mm"
include "3adant1.mm"
include "fvelimab.mm"
include "syl2anc.mm"
include "rexun.mm"
include "syl6bb.mm"
include "3adant3.mm"
include "3adant2.mm"
include "orbi12d.mm"
include "bitr4d.mm"
include "elun.mm"
include "syl6bbr.mm"
include "eqrdv.mm"

theorem unima
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vy: setvar y
  let vx: setvar x


  assert |- ( ( F Fn A /\ B C_ A /\ C C_ A ) -> ( F " ( B u. C ) ) = ( ( F " B ) u. ( F " C ) ) )

  proof
    cF
    cA
    wfn
    #
    cB
    cA
    wss
    #
    cC
    cA
    wss
    #
    w3a
    #
    vy
    cF
    cB
    cC
    cun
    #
    cima
    #
    cF
    cB
    cima
    #
    cF
    cC
    cima
    #
    cun
    #
    @3
    vy
    cv
    #
    @5
    wcel
    #
    @9
    @6
    wcel
    #
    @9
    @7
    wcel
    #
    wo
    #
    @9
    @8
    wcel
    @3
    @10
    vx
    cv
    cF
    cfv
    @9
    wceq
    #
    vx
    cB
    wrex
    #
    @14
    vx
    cC
    wrex
    #
    wo
    #
    @13
    @3
    @10
    @14
    vx
    @4
    wrex
    #
    @17
    @3
    @0
    @4
    cA
    wss
    #
    @10
    @18
    wb
    @0
    @1
    @2
    simp1
    @1
    @2
    @19
    @0
    @1
    @2
    wa
    cB
    cC
    cA
    @1
    @2
    simpl
    @1
    @2
    simpr
    unssd
    3adant1
    vx
    cA
    @4
    @9
    cF
    fvelimab
    syl2anc
    @14
    vx
    cB
    cC
    rexun
    syl6bb
    @3
    @11
    @15
    @12
    @16
    @0
    @1
    @11
    @15
    wb
    @2
    vx
    cA
    cB
    @9
    cF
    fvelimab
    3adant3
    @0
    @2
    @12
    @16
    wb
    @1
    vx
    cA
    cC
    @9
    cF
    fvelimab
    3adant2
    orbi12d
    bitr4d
    @9
    @6
    @7
    elun
    syl6bbr
    eqrdv
end
