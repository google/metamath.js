include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "co.mm"
include "cdiv.mm"
include "clog.mm"
include "cfv.mm"
include "cim.mm"
include "wceq.mm"
include "eldifsn.mm"
include "cv.mm"
include "oveq12.mm"
include "ancoms.mm"
include "fveq2d.mm"
include "fvex.mm"
include "ovmpt2a.mm"
include "syl2anbr.mm"

theorem angval
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cC: class C
  assume ang.1: |- F = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |-> ( Im ` ( log ` ( y / x ) ) ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) ) -> ( A F B ) = ( Im ` ( log ` ( B / A ) ) ) )

  proof
    cA
    cc
    wcel
    cA
    cc0
    wne
    wa
    cA
    cc
    cc0
    csn
    cdif
    #
    wcel
    cB
    @0
    wcel
    cA
    cB
    cF
    co
    cB
    cA
    cdiv
    co
    #
    clog
    cfv
    #
    cim
    cfv
    #
    wceq
    cB
    cc
    wcel
    cB
    cc0
    wne
    wa
    cA
    cc
    cc0
    eldifsn
    cB
    cc
    cc0
    eldifsn
    vx
    vy
    cA
    cB
    @0
    @0
    vy
    cv
    #
    vx
    cv
    #
    cdiv
    co
    #
    clog
    cfv
    #
    cim
    cfv
    @3
    cF
    @5
    cA
    wceq
    #
    @4
    cB
    wceq
    #
    wa
    #
    @7
    @2
    cim
    @10
    @6
    @1
    clog
    @9
    @8
    @6
    @1
    wceq
    @4
    cB
    @5
    cA
    cdiv
    oveq12
    ancoms
    fveq2d
    fveq2d
    ang.1
    @2
    cim
    fvex
    ovmpt2a
    syl2anbr
end
