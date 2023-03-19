include "com.mm"
include "wcel.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cuni.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "cdif.mm"
include "csuc.mm"
include "inf3lemd.mm"
include "inf3lem2.mm"
include "com12.mm"
include "pssdifn0.mm"
include "syl6an.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "cvv.mm"
include "vex.mm"
include "difexi.mm"
include "zfreg.mm"
include "mpan.mm"
include "wn.mm"
include "eldifi.mm"
include "inssdif0.mm"
include "biimpri.mm"
include "anim12i.mm"
include "fvex.mm"
include "inf3lema.mm"
include "sylibr.mm"
include "inf3lemc.mm"
include "eleq2d.mm"
include "syl5ibr.mm"
include "wi.mm"
include "eldifn.mm"
include "adantr.mm"
include "a1i.mm"
include "jcad.mm"
include "eleq2.mm"
include "biimprd.mm"
include "iman.mm"
include "sylib.mm"
include "necon2ai.mm"
include "syl6.mm"
include "expd.mm"
include "rexlimdv.mm"
include "syl5.mm"
include "syldc.mm"

theorem inf3lem3
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
  assert |- ( ( x =/= (/) /\ x C_ U. x ) -> ( A e. _om -> ( F ` A ) =/= ( F ` suc A ) ) )

  proof
    cA
    com
    wcel
    #
    vx
    cv
    #
    c0
    wne
    @1
    @1
    cuni
    wss
    wa
    #
    @1
    cA
    cF
    cfv
    #
    cdif
    #
    c0
    wne
    #
    @3
    cA
    csuc
    cF
    cfv
    #
    wne
    #
    @0
    @3
    @1
    wss
    @2
    @3
    @1
    wne
    #
    @5
    vx
    vy
    vw
    cA
    cB
    cF
    cG
    inf3lem.1
    inf3lem.2
    inf3lem.3
    inf3lem.4
    inf3lemd
    @2
    @0
    @8
    vx
    vy
    vw
    cA
    cB
    cF
    cG
    inf3lem.1
    inf3lem.2
    inf3lem.3
    inf3lem.4
    inf3lem2
    com12
    @3
    @1
    pssdifn0
    syl6an
    @5
    vv
    cv
    #
    @4
    cin
    c0
    wceq
    #
    vv
    @4
    wrex
    #
    @0
    @7
    @4
    cvv
    wcel
    @5
    @11
    @1
    @3
    vx
    vex
    difexi
    vv
    @4
    cvv
    zfreg
    mpan
    @0
    @10
    @7
    vv
    @4
    @0
    @9
    @4
    wcel
    #
    @10
    @7
    @0
    @12
    @10
    wa
    #
    @9
    @6
    wcel
    #
    @9
    @3
    wcel
    #
    wn
    #
    wa
    #
    @7
    @0
    @13
    @14
    @16
    @13
    @14
    @0
    @9
    @3
    cG
    cfv
    #
    wcel
    #
    @13
    @9
    @1
    wcel
    #
    @9
    @1
    cin
    @3
    wss
    #
    wa
    @19
    @12
    @20
    @10
    @21
    @9
    @1
    @3
    eldifi
    @21
    @10
    @9
    @1
    @3
    inssdif0
    biimpri
    anim12i
    vx
    vy
    vw
    @9
    @3
    cF
    cG
    inf3lem.1
    inf3lem.2
    vv
    vex
    cA
    cF
    fvex
    inf3lema
    sylibr
    @0
    @6
    @18
    @9
    vx
    vy
    vw
    cA
    cB
    cF
    cG
    inf3lem.1
    inf3lem.2
    inf3lem.3
    inf3lem.4
    inf3lemc
    eleq2d
    syl5ibr
    @13
    @16
    wi
    @0
    @12
    @16
    @10
    @9
    @1
    @3
    eldifn
    adantr
    a1i
    jcad
    @17
    @3
    @6
    @3
    @6
    wceq
    #
    @14
    @15
    wi
    @17
    wn
    @22
    @15
    @14
    @3
    @6
    @9
    eleq2
    biimprd
    @14
    @15
    iman
    sylib
    necon2ai
    syl6
    expd
    rexlimdv
    syl5
    syldc
end
