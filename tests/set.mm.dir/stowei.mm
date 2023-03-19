include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wtru.mm"
include "nfcv.mm"
include "nftru.mm"
include "ccmp.mm"
include "wcel.mm"
include "a1i.mm"
include "wss.mm"
include "caddc.mm"
include "cmpt.mm"
include "3adant1.mm"
include "cmul.mm"
include "cr.mm"
include "adantl.mm"
include "wne.mm"
include "w3a.mm"
include "crp.mm"
include "stoweid.mm"
include "trud.mm"

theorem stowei
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cC: class C
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cE: class E
  let cF: class F
  let cJ: class J
  let cK: class K
  let vr: setvar r
  let vk: setvar k
  assume stowei.1: |- K = ( topGen ` ran (,) )
  assume stowei.2: |- J e. Comp
  assume stowei.3: |- T = U. J
  assume stowei.4: |- C = ( J Cn K )
  assume stowei.5: |- A C_ C
  assume stowei.6: |- ( ( f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stowei.7: |- ( ( f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stowei.8: |- ( x e. RR -> ( t e. T |-> x ) e. A )
  assume stowei.9: |- ( ( r e. T /\ t e. T /\ r =/= t ) -> E. h e. A ( h ` r ) =/= ( h ` t ) )
  assume stowei.10: |- F e. C
  assume stowei.11: |- E e. RR+

  disjoint f g
  disjoint f t
  disjoint A f
  disjoint g t
  disjoint A g
  disjoint A t
  disjoint f h
  disjoint f r
  disjoint f x
  disjoint h r
  disjoint h t
  disjoint h x
  disjoint A h
  disjoint r t
  disjoint r x
  disjoint A r
  disjoint t x
  disjoint A x
  disjoint E f
  disjoint E g
  disjoint E t
  disjoint F f
  disjoint F g
  disjoint F t
  disjoint J f
  disjoint J r
  disjoint J t
  disjoint T f
  disjoint T g
  disjoint T t
  disjoint E h
  disjoint E r
  disjoint E x
  disjoint F h
  disjoint F r
  disjoint F x
  disjoint T h
  disjoint T r
  disjoint T x
  disjoint K t
  disjoint k x
  assert |- E. f e. A A. t e. T ( abs ` ( ( f ` t ) - ( F ` t ) ) ) < E

  proof
    vt
    cv
    #
    vf
    cv
    #
    cfv
    #
    @0
    cF
    cfv
    cmin
    co
    cabs
    cfv
    cE
    clt
    wbr
    vt
    cT
    wral
    vf
    cA
    wrex
    wtru
    vx
    vt
    cA
    cC
    cT
    vf
    vg
    vh
    cE
    cF
    cJ
    cK
    vr
    vt
    cF
    nfcv
    vt
    nftru
    stowei.1
    cJ
    ccmp
    wcel
    wtru
    stowei.2
    a1i
    stowei.3
    stowei.4
    cA
    cC
    wss
    wtru
    stowei.5
    a1i
    @1
    cA
    wcel
    #
    vg
    cv
    #
    cA
    wcel
    #
    vt
    cT
    @2
    @0
    @4
    cfv
    #
    caddc
    co
    cmpt
    cA
    wcel
    wtru
    stowei.6
    3adant1
    @3
    @5
    vt
    cT
    @2
    @6
    cmul
    co
    cmpt
    cA
    wcel
    wtru
    stowei.7
    3adant1
    vx
    cv
    #
    cr
    wcel
    vt
    cT
    @7
    cmpt
    cA
    wcel
    wtru
    stowei.8
    adantl
    vr
    cv
    #
    cT
    wcel
    @0
    cT
    wcel
    @8
    @0
    wne
    w3a
    @8
    vh
    cv
    #
    cfv
    @0
    @9
    cfv
    wne
    vh
    cA
    wrex
    wtru
    stowei.9
    adantl
    cF
    cC
    wcel
    wtru
    stowei.10
    a1i
    cE
    crp
    wcel
    wtru
    stowei.11
    a1i
    stoweid
    trud
end
