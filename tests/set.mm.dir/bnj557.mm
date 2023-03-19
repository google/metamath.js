include "w-bnj15.mm"
include "w-bnj17.mm"
include "w3a.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "cfv.mm"
include "wa.mm"
include "3an4anass.mm"
include "bnj556.mm"
include "3anim3i.mm"
include "com.mm"
include "csuc.mm"
include "vex.mm"
include "bnj216.mm"
include "bnj837.mm"
include "anim12i.mm"
include "sylbir.mm"
include "bnj1254.mm"
include "simp3bi.mm"
include "bnj551.mm"
include "syl2an.mm"
include "adantl.mm"
include "jca.mm"
include "bnj256.mm"
include "df-3an.mm"
include "3imtr4i.mm"
include "bnj553.mm"
include "syl.mm"

theorem bnj557
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
  assume bnj557.3: |- D = ( _om \ { (/) } )
  assume bnj557.16: |- G = ( f u. { <. m , U_ y e. ( f ` p ) _pred ( y , A , R ) >. } )
  assume bnj557.17: |- ( ta <-> ( f Fn m /\ ph' /\ ps' ) )
  assume bnj557.18: |- ( si <-> ( m e. D /\ n = suc m /\ p e. m ) )
  assume bnj557.19: |- ( et <-> ( m e. D /\ n = suc m /\ p e. _om /\ m = suc p ) )
  assume bnj557.20: |- ( ze <-> ( i e. _om /\ suc i e. n /\ m = suc i ) )
  assume bnj557.21: |- B = U_ y e. ( f ` i ) _pred ( y , A , R )
  assume bnj557.22: |- C = U_ y e. ( f ` p ) _pred ( y , A , R )
  assume bnj557.23: |- K = U_ y e. ( G ` i ) _pred ( y , A , R )
  assume bnj557.24: |- L = U_ y e. ( G ` p ) _pred ( y , A , R )
  assume bnj557.25: |- G = ( f u. { <. m , C >. } )
  assume bnj557.28: |- ( ph' <-> ( f ` (/) ) = _pred ( x , A , R ) )
  assume bnj557.29: |- ( ps' <-> A. i e. _om ( suc i e. m -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj557.36: |- ( ( R _FrSe A /\ ta /\ si ) -> G Fn n )

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
  assert |- ( ( R _FrSe A /\ ta /\ et /\ ze ) -> ( G ` m ) = L )

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
    @0
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
    @3
    wceq
    #
    w3a
    #
    @4
    cG
    cfv
    cL
    wceq
    @0
    wta
    wa
    #
    wet
    wze
    wa
    #
    wa
    #
    @2
    @5
    wa
    #
    @7
    wa
    @1
    @8
    @11
    @12
    @7
    @11
    @0
    wta
    wet
    w3a
    #
    wze
    wa
    @12
    @0
    wta
    wet
    wze
    3an4anass
    @13
    @2
    wze
    @5
    wet
    wsi
    @0
    wta
    wet
    wsi
    cD
    vm
    vn
    vp
    bnj557.18
    bnj557.19
    bnj556
    3anim3i
    @3
    com
    wcel
    #
    @3
    csuc
    #
    vn
    cv
    #
    wcel
    #
    @4
    @15
    wceq
    #
    @5
    wze
    bnj557.20
    @4
    @3
    vi
    vex
    bnj216
    bnj837
    anim12i
    sylbir
    @10
    @7
    @9
    wet
    @4
    @6
    csuc
    wceq
    #
    @18
    @7
    wze
    wet
    @4
    cD
    wcel
    @16
    @4
    csuc
    wceq
    @6
    com
    wcel
    @19
    bnj557.19
    bnj1254
    wze
    @14
    @17
    @18
    bnj557.20
    simp3bi
    vi
    vm
    vp
    bnj551
    syl2an
    adantl
    jca
    @0
    wta
    wet
    wze
    bnj256
    @2
    @5
    @7
    df-3an
    3imtr4i
    wta
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
    bnj557.28
    bnj557.29
    bnj557.3
    bnj557.16
    bnj557.17
    bnj557.18
    bnj557.22
    bnj557.25
    bnj557.21
    bnj557.23
    bnj557.24
    bnj557.36
    bnj553
    syl
end
