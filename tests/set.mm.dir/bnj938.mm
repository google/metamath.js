include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "w-bnj15.mm"
include "wcel.mm"
include "w-bnj17.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "cvv.mm"
include "elisset.mm"
include "bnj706.mm"
include "wi.mm"
include "wfn.mm"
include "c0.mm"
include "w3a.mm"
include "bnj291.mm"
include "simplbi.mm"
include "bnj602.mm"
include "eqeq2d.mm"
include "syl6bbr.mm"
include "3anbi2d.mm"
include "syl5ibr.mm"
include "biid.mm"
include "bnj546.mm"
include "syl6.mm"
include "exlimiv.mm"
include "mpcom.mm"

theorem bnj938
  let wta: wff ta
  let wsi: wff si
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cX: class X
  let vp: setvar p
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let vx: setvar x
  assume bnj938.1: |- D = ( _om \ { (/) } )
  assume bnj938.2: |- ( ta <-> ( f Fn m /\ ph' /\ ps' ) )
  assume bnj938.3: |- ( si <-> ( m e. D /\ n = suc m /\ p e. m ) )
  assume bnj938.4: |- ( ph' <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj938.5: |- ( ps' <-> A. i e. _om ( suc i e. m -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )

  disjoint A i
  disjoint A p
  disjoint A y
  disjoint i p
  disjoint i y
  disjoint p y
  disjoint R i
  disjoint R p
  disjoint R y
  disjoint f i
  disjoint f p
  disjoint f y
  disjoint i m
  disjoint m p
  disjoint A x
  disjoint p x
  disjoint x y
  disjoint R x
  disjoint X x
  disjoint f x
  disjoint si x
  disjoint ta x
  assert |- ( ( R _FrSe A /\ X e. A /\ ta /\ si ) -> U_ y e. ( f ` p ) _pred ( y , A , R ) e. _V )

  proof
    vx
    cv
    #
    cX
    wceq
    #
    vx
    wex
    #
    cA
    cR
    w-bnj15
    #
    cX
    cA
    wcel
    #
    wta
    wsi
    w-bnj17
    #
    vy
    vp
    cv
    vf
    cv
    #
    cfv
    cA
    cR
    vy
    cv
    c-bnj14
    ciun
    cvv
    wcel
    #
    @3
    @4
    wta
    wsi
    @2
    vx
    cX
    cA
    elisset
    bnj706
    @1
    @5
    @7
    wi
    vx
    @1
    @5
    @3
    @6
    vm
    cv
    wfn
    #
    c0
    @6
    cfv
    #
    cA
    cR
    @0
    c-bnj14
    #
    wceq
    #
    bnjwpsm
    w3a
    #
    wsi
    w3a
    #
    @7
    @5
    @13
    @1
    @3
    wta
    wsi
    w3a
    #
    @5
    @14
    @4
    @3
    @4
    wta
    wsi
    bnj291
    simplbi
    @1
    @12
    wta
    @3
    wsi
    @1
    @12
    @8
    bnjwphm
    bnjwpsm
    w3a
    wta
    @1
    @11
    bnjwphm
    @8
    bnjwpsm
    @1
    @11
    @9
    cA
    cR
    cX
    c-bnj14
    #
    wceq
    bnjwphm
    @1
    @10
    @15
    @9
    cA
    cR
    @0
    cX
    bnj602
    eqeq2d
    bnj938.4
    syl6bbr
    3anbi2d
    bnj938.2
    syl6bbr
    3anbi2d
    syl5ibr
    @12
    wsi
    vx
    vy
    cA
    cD
    cR
    vf
    vi
    vm
    vn
    vp
    @11
    bnjwpsm
    bnj938.1
    @12
    biid
    bnj938.3
    @11
    biid
    bnj938.5
    bnj546
    syl6
    exlimiv
    mpcom
end
