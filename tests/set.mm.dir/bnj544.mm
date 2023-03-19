include "w-bnj15.mm"
include "cv.mm"
include "com.mm"
include "wcel.mm"
include "csuc.mm"
include "wceq.mm"
include "w3a.mm"
include "wfn.mm"
include "bnj923.mm"
include "3anim1i.mm"
include "sylbi.mm"
include "biid.mm"
include "bnj543.mm"
include "syl3an3.mm"

theorem bnj544
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
  let cG: class G
  let vp: setvar p
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  assume bnj544.1: |- ( ph' <-> ( f ` (/) ) = _pred ( x , A , R ) )
  assume bnj544.2: |- ( ps' <-> A. i e. _om ( suc i e. m -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj544.3: |- D = ( _om \ { (/) } )
  assume bnj544.4: |- G = ( f u. { <. m , U_ y e. ( f ` p ) _pred ( y , A , R ) >. } )
  assume bnj544.5: |- ( ta <-> ( f Fn m /\ ph' /\ ps' ) )
  assume bnj544.6: |- ( si <-> ( m e. D /\ n = suc m /\ p e. m ) )

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
  assert |- ( ( R _FrSe A /\ ta /\ si ) -> G Fn n )

  proof
    wsi
    cA
    cR
    w-bnj15
    wta
    vm
    cv
    #
    com
    wcel
    #
    vn
    cv
    #
    @0
    csuc
    wceq
    #
    vp
    cv
    @0
    wcel
    #
    w3a
    #
    cG
    @2
    wfn
    wsi
    @0
    cD
    wcel
    #
    @3
    @4
    w3a
    @5
    bnj544.6
    @6
    @1
    @3
    @4
    cD
    vm
    bnj544.3
    bnj923
    3anim1i
    sylbi
    wta
    @5
    vx
    vy
    cA
    cR
    vf
    vi
    vm
    vn
    cG
    vp
    bnjwphm
    bnjwpsm
    bnj544.1
    bnj544.2
    bnj544.4
    bnj544.5
    @5
    biid
    bnj543
    syl3an3
end
