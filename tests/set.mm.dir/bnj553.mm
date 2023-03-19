include "w-bnj15.mm"
include "w3a.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "cfv.mm"
include "wfun.mm"
include "cop.mm"
include "bnj930.mm"
include "csn.mm"
include "cun.mm"
include "opex.mm"
include "snid.mm"
include "elun2.mm"
include "ax-mp.mm"
include "eleqtrri.mm"
include "funopfv.mm"
include "mpisyl.mm"
include "3ad2ant1.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "fveq2.mm"
include "bnj1113.mm"
include "3eqtr4g.mm"
include "3ad2ant3.mm"
include "bnj548.mm"
include "3adant3.mm"
include "eqeq12i.mm"
include "eqcom.mm"
include "bitri.mm"
include "sylibr.mm"
include "3eqtr2rd.mm"
include "eqtrd.mm"

theorem bnj553
  let wta: wff ta
  let wsi: wff si
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let cK: class K
  let cL: class L
  let vp: setvar p
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  assume bnj553.1: |- ( ph' <-> ( f ` (/) ) = _pred ( x , A , R ) )
  assume bnj553.2: |- ( ps' <-> A. i e. _om ( suc i e. m -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj553.3: |- D = ( _om \ { (/) } )
  assume bnj553.4: |- G = ( f u. { <. m , U_ y e. ( f ` p ) _pred ( y , A , R ) >. } )
  assume bnj553.5: |- ( ta <-> ( f Fn m /\ ph' /\ ps' ) )
  assume bnj553.6: |- ( si <-> ( m e. D /\ n = suc m /\ p e. m ) )
  assume bnj553.7: |- C = U_ y e. ( f ` p ) _pred ( y , A , R )
  assume bnj553.8: |- G = ( f u. { <. m , C >. } )
  assume bnj553.9: |- B = U_ y e. ( f ` i ) _pred ( y , A , R )
  assume bnj553.10: |- K = U_ y e. ( G ` i ) _pred ( y , A , R )
  assume bnj553.11: |- L = U_ y e. ( G ` p ) _pred ( y , A , R )
  assume bnj553.12: |- ( ( R _FrSe A /\ ta /\ si ) -> G Fn n )

  disjoint A i
  disjoint A p
  disjoint A y
  disjoint i p
  disjoint i y
  disjoint p y
  disjoint G y
  disjoint R i
  disjoint R p
  disjoint R y
  disjoint f i
  disjoint f p
  disjoint f y
  disjoint i m
  disjoint m p
  disjoint p ph'
  assert |- ( ( ( R _FrSe A /\ ta /\ si ) /\ i e. m /\ p = i ) -> ( G ` m ) = L )

  proof
    cA
    cR
    w-bnj15
    wta
    wsi
    w3a
    #
    vi
    cv
    #
    vm
    cv
    #
    wcel
    #
    vp
    cv
    #
    @1
    wceq
    #
    w3a
    #
    @2
    cG
    cfv
    #
    cC
    cL
    @0
    @3
    @7
    cC
    wceq
    #
    @5
    @0
    cG
    wfun
    @2
    cC
    cop
    #
    cG
    wcel
    @8
    @0
    vn
    cv
    cG
    bnj553.12
    bnj930
    @9
    vf
    cv
    #
    @9
    csn
    #
    cun
    #
    cG
    @9
    @11
    wcel
    @9
    @12
    wcel
    @9
    @2
    cC
    opex
    snid
    @9
    @11
    @10
    elun2
    ax-mp
    bnj553.8
    eleqtrri
    @2
    cC
    cG
    funopfv
    mpisyl
    3ad2ant1
    @6
    cL
    cK
    cB
    cC
    @5
    @0
    cL
    cK
    wceq
    @3
    @5
    vy
    @4
    cG
    cfv
    #
    cA
    cR
    vy
    cv
    c-bnj14
    #
    ciun
    vy
    @1
    cG
    cfv
    #
    @14
    ciun
    cL
    cK
    vy
    @4
    @1
    @13
    @15
    @14
    @4
    @1
    cG
    fveq2
    bnj1113
    bnj553.11
    bnj553.10
    3eqtr4g
    3ad2ant3
    @0
    @3
    cB
    cK
    wceq
    @5
    wta
    wsi
    vy
    cA
    cB
    vy
    @4
    @10
    cfv
    #
    @14
    ciun
    #
    cR
    vf
    vi
    vm
    vn
    cG
    cK
    bnjwphm
    bnjwpsm
    bnj553.5
    bnj553.9
    bnj553.10
    bnj553.4
    bnj553.12
    bnj548
    3adant3
    @5
    @0
    cB
    cC
    wceq
    #
    @3
    @5
    @17
    vy
    @1
    @10
    cfv
    #
    @14
    ciun
    #
    wceq
    #
    @18
    vy
    @4
    @1
    @16
    @19
    @14
    @4
    @1
    @10
    fveq2
    bnj1113
    @18
    @20
    @17
    wceq
    @21
    cB
    @20
    cC
    @17
    bnj553.9
    bnj553.7
    eqeq12i
    @20
    @17
    eqcom
    bitri
    sylibr
    3ad2ant3
    3eqtr2rd
    eqtrd
end
