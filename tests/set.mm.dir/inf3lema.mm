include "cv.mm"
include "cin.mm"
include "wss.mm"
include "cfv.mm"
include "wceq.mm"
include "ineq1.mm"
include "sseq1d.mm"
include "cvv.mm"
include "wcel.mm"
include "crab.mm"
include "sseq2.mm"
include "rabbidv.mm"
include "cmpt.mm"
include "cbvrabv.mm"
include "syl6eq.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "vex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "elrab2.mm"

theorem inf3lema
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  assume inf3lem.1: |- G = ( y e. _V |-> { w e. x | ( w i^i x ) C_ y } )
  assume inf3lem.2: |- F = ( rec ( G , (/) ) |` _om )
  assume inf3lem.3: |- A e. _V
  assume inf3lem.4: |- B e. _V

  disjoint x y
  disjoint w x
  disjoint w y
  disjoint v x
  disjoint u x
  disjoint f x
  disjoint v y
  disjoint u y
  disjoint f y
  disjoint v w
  disjoint u w
  disjoint f w
  disjoint u v
  disjoint f v
  disjoint f u
  disjoint G v
  disjoint G u
  disjoint G f
  disjoint F v
  disjoint F u
  disjoint F f
  disjoint A v
  disjoint A u
  disjoint A f
  disjoint B v
  disjoint B u
  disjoint B f
  assert |- ( A e. ( G ` B ) <-> ( A e. x /\ ( A i^i x ) C_ B ) )

  proof
    vf
    cv
    #
    vx
    cv
    #
    cin
    #
    cB
    wss
    #
    cA
    @1
    cin
    #
    cB
    wss
    vf
    cA
    @1
    cB
    cG
    cfv
    #
    @0
    cA
    wceq
    @2
    @4
    cB
    @0
    cA
    @1
    ineq1
    sseq1d
    cB
    cvv
    wcel
    @5
    @3
    vf
    @1
    crab
    #
    wceq
    inf3lem.4
    vv
    cB
    @2
    vv
    cv
    #
    wss
    #
    vf
    @1
    crab
    #
    @6
    cvv
    cG
    @7
    cB
    wceq
    @8
    @3
    vf
    @1
    @7
    cB
    @2
    sseq2
    rabbidv
    cG
    vy
    cvv
    vw
    cv
    #
    @1
    cin
    #
    vy
    cv
    #
    wss
    #
    vw
    @1
    crab
    #
    cmpt
    vv
    cvv
    @9
    cmpt
    inf3lem.1
    vy
    vv
    cvv
    @14
    @9
    @12
    @7
    wceq
    #
    @14
    @11
    @7
    wss
    #
    vw
    @1
    crab
    @9
    @15
    @13
    @16
    vw
    @1
    @12
    @7
    @11
    sseq2
    rabbidv
    @16
    @8
    vw
    vf
    @1
    @10
    @0
    wceq
    @11
    @2
    @7
    @10
    @0
    @1
    ineq1
    sseq1d
    cbvrabv
    syl6eq
    cbvmptv
    eqtri
    @3
    vf
    @1
    vx
    vex
    rabex
    fvmpt
    ax-mp
    elrab2
end
