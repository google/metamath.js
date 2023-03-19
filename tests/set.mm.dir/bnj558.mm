include "w-bnj15.mm"
include "w-bnj17.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "csuc.mm"
include "bnj557.mm"
include "wa.mm"
include "wb.mm"
include "w3a.mm"
include "bnj422.mm"
include "bnj253.mm"
include "bitri.mm"
include "simp1bi.mm"
include "bnj554.mm"
include "syl.mm"
include "mpbid.mm"

theorem bnj558
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
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
  assume bnj558.3: |- D = ( _om \ { (/) } )
  assume bnj558.16: |- G = ( f u. { <. m , U_ y e. ( f ` p ) _pred ( y , A , R ) >. } )
  assume bnj558.17: |- ( ta <-> ( f Fn m /\ ph' /\ ps' ) )
  assume bnj558.18: |- ( si <-> ( m e. D /\ n = suc m /\ p e. m ) )
  assume bnj558.19: |- ( et <-> ( m e. D /\ n = suc m /\ p e. _om /\ m = suc p ) )
  assume bnj558.20: |- ( ze <-> ( i e. _om /\ suc i e. n /\ m = suc i ) )
  assume bnj558.21: |- B = U_ y e. ( f ` i ) _pred ( y , A , R )
  assume bnj558.22: |- C = U_ y e. ( f ` p ) _pred ( y , A , R )
  assume bnj558.23: |- K = U_ y e. ( G ` i ) _pred ( y , A , R )
  assume bnj558.24: |- L = U_ y e. ( G ` p ) _pred ( y , A , R )
  assume bnj558.25: |- G = ( f u. { <. m , C >. } )
  assume bnj558.28: |- ( ph' <-> ( f ` (/) ) = _pred ( x , A , R ) )
  assume bnj558.29: |- ( ps' <-> A. i e. _om ( suc i e. m -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj558.36: |- ( ( R _FrSe A /\ ta /\ si ) -> G Fn n )

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
  assert |- ( ( R _FrSe A /\ ta /\ et /\ ze ) -> ( G ` suc i ) = K )

  proof
    cA
    cR
    w-bnj15
    #
    wta
    wet
    wze
    w-bnj17
    #
    vm
    cv
    cG
    cfv
    cL
    wceq
    #
    vi
    cv
    csuc
    cG
    cfv
    cK
    wceq
    #
    wta
    wet
    wze
    wsi
    vx
    vy
    cA
    cB
    cC
    cD
    cR
    vf
    vi
    vm
    vn
    cG
    cK
    cL
    vp
    bnjwphm
    bnjwpsm
    bnj558.3
    bnj558.16
    bnj558.17
    bnj558.18
    bnj558.19
    bnj558.20
    bnj558.21
    bnj558.22
    bnj558.23
    bnj558.24
    bnj558.25
    bnj558.28
    bnj558.29
    bnj558.36
    bnj557
    @1
    wet
    wze
    wa
    #
    @2
    @3
    wb
    @1
    @4
    @0
    wta
    @1
    wet
    wze
    @0
    wta
    w-bnj17
    @4
    @0
    wta
    w3a
    @0
    wta
    wet
    wze
    bnj422
    wet
    wze
    @0
    wta
    bnj253
    bitri
    simp1bi
    wet
    wze
    vy
    cA
    cD
    cR
    vi
    vm
    vn
    cG
    cK
    cL
    vp
    bnj558.19
    bnj558.20
    bnj558.23
    bnj558.24
    bnj558.23
    bnj558.24
    bnj554
    syl
    mpbid
end
