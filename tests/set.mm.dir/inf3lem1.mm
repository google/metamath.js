include "cv.mm"
include "cfv.mm"
include "csuc.mm"
include "wss.mm"
include "c0.mm"
include "wceq.mm"
include "fveq2.mm"
include "suceq.mm"
include "fveq2d.mm"
include "sseq12d.mm"
include "inf3lemb.mm"
include "0ss.mm"
include "eqsstri.mm"
include "com.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "cin.mm"
include "sstr2.mm"
include "com12.mm"
include "anim2d.mm"
include "vex.mm"
include "inf3lemc.mm"
include "eleq2d.mm"
include "fvex.mm"
include "inf3lema.mm"
include "syl6bb.mm"
include "peano2b.mm"
include "sucex.mm"
include "sylbi.mm"
include "imbi12d.mm"
include "syl5ibr.mm"
include "imp.mm"
include "ssrdv.mm"
include "ex.mm"
include "finds.mm"

theorem inf3lem1
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
  assert |- ( A e. _om -> ( F ` A ) C_ ( F ` suc A ) )

  proof
    vv
    cv
    #
    cF
    cfv
    #
    @0
    csuc
    #
    cF
    cfv
    #
    wss
    c0
    cF
    cfv
    #
    c0
    csuc
    #
    cF
    cfv
    #
    wss
    vu
    cv
    #
    cF
    cfv
    #
    @7
    csuc
    #
    cF
    cfv
    #
    wss
    #
    @10
    @9
    csuc
    #
    cF
    cfv
    #
    wss
    #
    cA
    cF
    cfv
    #
    cA
    csuc
    #
    cF
    cfv
    #
    wss
    vv
    vu
    cA
    @0
    c0
    wceq
    #
    @1
    @4
    @3
    @6
    @0
    c0
    cF
    fveq2
    @18
    @2
    @5
    cF
    @0
    c0
    suceq
    fveq2d
    sseq12d
    @0
    @7
    wceq
    #
    @1
    @8
    @3
    @10
    @0
    @7
    cF
    fveq2
    @19
    @2
    @9
    cF
    @0
    @7
    suceq
    fveq2d
    sseq12d
    @0
    @9
    wceq
    #
    @1
    @10
    @3
    @13
    @0
    @9
    cF
    fveq2
    @20
    @2
    @12
    cF
    @0
    @9
    suceq
    fveq2d
    sseq12d
    @0
    cA
    wceq
    #
    @1
    @15
    @3
    @17
    @0
    cA
    cF
    fveq2
    @21
    @2
    @16
    cF
    @0
    cA
    suceq
    fveq2d
    sseq12d
    @4
    c0
    @6
    vx
    vy
    vw
    cA
    cA
    cF
    cG
    inf3lem.1
    inf3lem.2
    inf3lem.3
    inf3lem.3
    inf3lemb
    @6
    0ss
    eqsstri
    @7
    com
    wcel
    #
    @11
    @14
    @22
    @11
    wa
    vv
    @10
    @13
    @22
    @11
    @0
    @10
    wcel
    #
    @0
    @13
    wcel
    #
    wi
    #
    @11
    @25
    @22
    @0
    vx
    cv
    #
    wcel
    #
    @0
    @26
    cin
    #
    @8
    wss
    #
    wa
    #
    @27
    @28
    @10
    wss
    #
    wa
    #
    wi
    @11
    @29
    @31
    @27
    @29
    @11
    @31
    @28
    @8
    @10
    sstr2
    com12
    anim2d
    @22
    @23
    @30
    @24
    @32
    @22
    @23
    @0
    @8
    cG
    cfv
    #
    wcel
    @30
    @22
    @10
    @33
    @0
    vx
    vy
    vw
    @7
    cA
    cF
    cG
    inf3lem.1
    inf3lem.2
    vu
    vex
    #
    inf3lem.3
    inf3lemc
    eleq2d
    vx
    vy
    vw
    @0
    @8
    cF
    cG
    inf3lem.1
    inf3lem.2
    vv
    vex
    #
    @7
    cF
    fvex
    inf3lema
    syl6bb
    @22
    @24
    @0
    @10
    cG
    cfv
    #
    wcel
    @32
    @22
    @13
    @36
    @0
    @22
    @9
    com
    wcel
    @13
    @36
    wceq
    @7
    peano2b
    vx
    vy
    vw
    @9
    cA
    cF
    cG
    inf3lem.1
    inf3lem.2
    @7
    @34
    sucex
    inf3lem.3
    inf3lemc
    sylbi
    eleq2d
    vx
    vy
    vw
    @0
    @10
    cF
    cG
    inf3lem.1
    inf3lem.2
    @35
    @9
    cF
    fvex
    inf3lema
    syl6bb
    imbi12d
    syl5ibr
    imp
    ssrdv
    ex
    finds
end
