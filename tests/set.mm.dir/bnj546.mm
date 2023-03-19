include "w-bnj15.mm"
include "w3a.mm"
include "cv.mm"
include "com.mm"
include "wcel.mm"
include "w-bnj17.mm"
include "wa.mm"
include "c-bnj14.mm"
include "cvv.mm"
include "cfv.mm"
include "wral.mm"
include "ciun.mm"
include "wfn.mm"
include "3simpc.mm"
include "sylbi.mm"
include "csuc.mm"
include "wceq.mm"
include "bnj923.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "jca.mm"
include "anim12i.mm"
include "bnj256.mm"
include "sylibr.mm"
include "anim2i.mm"
include "3impb.mm"
include "biid.mm"
include "bnj518.mm"
include "fvex.mm"
include "iunexg.mm"
include "mpan.mm"
include "3syl.mm"

theorem bnj546
  let wta: wff ta
  let wsi: wff si
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  assume bnj546.1: |- D = ( _om \ { (/) } )
  assume bnj546.2: |- ( ta <-> ( f Fn m /\ ph' /\ ps' ) )
  assume bnj546.3: |- ( si <-> ( m e. D /\ n = suc m /\ p e. m ) )
  assume bnj546.4: |- ( ph' <-> ( f ` (/) ) = _pred ( x , A , R ) )
  assume bnj546.5: |- ( ps' <-> A. i e. _om ( suc i e. m -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )

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
  disjoint p ph'
  assert |- ( ( R _FrSe A /\ ta /\ si ) -> U_ y e. ( f ` p ) _pred ( y , A , R ) e. _V )

  proof
    cA
    cR
    w-bnj15
    #
    wta
    wsi
    w3a
    @0
    bnjwphm
    bnjwpsm
    vm
    cv
    #
    com
    wcel
    #
    vp
    cv
    #
    @1
    wcel
    #
    w-bnj17
    #
    wa
    #
    cA
    cR
    vy
    cv
    c-bnj14
    #
    cvv
    wcel
    vy
    @3
    vf
    cv
    #
    cfv
    #
    wral
    #
    vy
    @9
    @7
    ciun
    cvv
    wcel
    #
    @0
    wta
    wsi
    @6
    wta
    wsi
    wa
    #
    @5
    @0
    @12
    bnjwphm
    bnjwpsm
    wa
    #
    @2
    @4
    wa
    #
    wa
    @5
    wta
    @13
    wsi
    @14
    wta
    @8
    @1
    wfn
    #
    bnjwphm
    bnjwpsm
    w3a
    @13
    bnj546.2
    @15
    bnjwphm
    bnjwpsm
    3simpc
    sylbi
    wsi
    @1
    cD
    wcel
    #
    vn
    cv
    @1
    csuc
    wceq
    #
    @4
    w3a
    #
    @14
    bnj546.3
    @18
    @2
    @4
    @16
    @17
    @2
    @4
    cD
    vm
    bnj546.1
    bnj923
    3ad2ant1
    @16
    @17
    @4
    simp3
    jca
    sylbi
    anim12i
    bnjwphm
    bnjwpsm
    @2
    @4
    bnj256
    sylibr
    anim2i
    3impb
    bnjwphm
    bnjwpsm
    @5
    vx
    vy
    cA
    cR
    vf
    vi
    vm
    vp
    bnj546.4
    bnj546.5
    @5
    biid
    bnj518
    @9
    cvv
    wcel
    @10
    @11
    @3
    @8
    fvex
    vy
    @9
    @7
    cvv
    cvv
    iunexg
    mpan
    3syl
end
