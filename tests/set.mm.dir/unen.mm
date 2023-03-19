include "cen.mm"
include "wbr.mm"
include "wa.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cun.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "wi.mm"
include "bren.mm"
include "eeanv.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "unex.mm"
include "f1oun.mm"
include "f1oen3g.mm"
include "sylancr.mm"
include "ex.mm"
include "exlimivv.mm"
include "sylbir.mm"
include "syl2anb.mm"
include "imp.mm"

theorem unen
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  let cV: class V


  assert |- ( ( ( A ~~ B /\ C ~~ D ) /\ ( ( A i^i C ) = (/) /\ ( B i^i D ) = (/) ) ) -> ( A u. C ) ~~ ( B u. D ) )

  proof
    cA
    cB
    cen
    wbr
    #
    cC
    cD
    cen
    wbr
    #
    wa
    cA
    cC
    cin
    c0
    wceq
    cB
    cD
    cin
    c0
    wceq
    wa
    #
    cA
    cC
    cun
    #
    cB
    cD
    cun
    #
    cen
    wbr
    #
    @0
    cA
    cB
    vx
    cv
    #
    wf1o
    #
    vx
    wex
    #
    cC
    cD
    vy
    cv
    #
    wf1o
    #
    vy
    wex
    #
    @2
    @5
    wi
    #
    @1
    cA
    cB
    vx
    bren
    cC
    cD
    vy
    bren
    @8
    @11
    wa
    @7
    @10
    wa
    #
    vy
    wex
    vx
    wex
    @12
    @7
    @10
    vx
    vy
    eeanv
    @13
    @12
    vx
    vy
    @13
    @2
    @5
    @13
    @2
    wa
    @6
    @9
    cun
    #
    cvv
    wcel
    @3
    @4
    @14
    wf1o
    @5
    @6
    @9
    vx
    vex
    vy
    vex
    unex
    cA
    cB
    cC
    cD
    @6
    @9
    f1oun
    @3
    @4
    @14
    cvv
    f1oen3g
    sylancr
    ex
    exlimivv
    sylbir
    syl2anb
    imp
end
