include "w-bnj15.mm"
include "w3a.mm"
include "cv.mm"
include "com.mm"
include "wcel.mm"
include "csuc.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "nfv.mm"
include "wfn.mm"
include "wral.mm"
include "nfra1.mm"
include "nfxfr.mm"
include "nf3an.mm"
include "wa.mm"
include "w-bnj17.mm"
include "df-bnj17.mm"
include "3anass.mm"
include "3anrot.mm"
include "df-3an.mm"
include "bitri.mm"
include "anbi2i.mm"
include "3bitr4ri.mm"
include "bnj558.mm"
include "sylbir.mm"
include "3expib.mm"
include "wne.mm"
include "bnj570.mm"
include "pm2.61ine.mm"
include "syl6eq.mm"
include "exp32.mm"
include "alrimi.mm"
include "bnj946.mm"
include "sylibr.mm"

theorem bnj571
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let wrh: wff rh
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
  let bnjwpsn: wff ps"
  assume bnj571.3: |- D = ( _om \ { (/) } )
  assume bnj571.16: |- G = ( f u. { <. m , U_ y e. ( f ` p ) _pred ( y , A , R ) >. } )
  assume bnj571.17: |- ( ta <-> ( f Fn m /\ ph' /\ ps' ) )
  assume bnj571.18: |- ( si <-> ( m e. D /\ n = suc m /\ p e. m ) )
  assume bnj571.19: |- ( et <-> ( m e. D /\ n = suc m /\ p e. _om /\ m = suc p ) )
  assume bnj571.20: |- ( ze <-> ( i e. _om /\ suc i e. n /\ m = suc i ) )
  assume bnj571.22: |- B = U_ y e. ( f ` i ) _pred ( y , A , R )
  assume bnj571.23: |- C = U_ y e. ( f ` p ) _pred ( y , A , R )
  assume bnj571.24: |- K = U_ y e. ( G ` i ) _pred ( y , A , R )
  assume bnj571.25: |- L = U_ y e. ( G ` p ) _pred ( y , A , R )
  assume bnj571.26: |- G = ( f u. { <. m , C >. } )
  assume bnj571.29: |- ( ph' <-> ( f ` (/) ) = _pred ( x , A , R ) )
  assume bnj571.30: |- ( ps' <-> A. i e. _om ( suc i e. m -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj571.38: |- ( ( R _FrSe A /\ ta /\ si ) -> G Fn n )
  assume bnj571.21: |- ( rh <-> ( i e. _om /\ suc i e. n /\ m =/= suc i ) )
  assume bnj571.40: |- ( ( R _FrSe A /\ ta /\ et ) -> G Fn n )
  assume bnj571.33: |- ( ps" <-> A. i e. _om ( suc i e. n -> ( G ` suc i ) = U_ y e. ( G ` i ) _pred ( y , A , R ) ) )

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
  disjoint et i
  disjoint f i
  disjoint f p
  disjoint f y
  disjoint i m
  disjoint m p
  disjoint i ph'
  disjoint p ph'
  assert |- ( ( R _FrSe A /\ ta /\ et ) -> ps" )

  proof
    cA
    cR
    w-bnj15
    #
    wta
    wet
    w3a
    #
    vi
    cv
    #
    com
    wcel
    #
    @2
    csuc
    #
    vn
    cv
    wcel
    #
    @4
    cG
    cfv
    #
    vy
    @2
    cG
    cfv
    cA
    cR
    vy
    cv
    c-bnj14
    #
    ciun
    #
    wceq
    #
    wi
    #
    wi
    #
    vi
    wal
    bnjwpsn
    @1
    @11
    vi
    @0
    wta
    wet
    vi
    @0
    vi
    nfv
    wta
    vf
    cv
    #
    vm
    cv
    #
    wfn
    #
    bnjwphm
    bnjwpsm
    w3a
    vi
    bnj571.17
    @14
    bnjwphm
    bnjwpsm
    vi
    @14
    vi
    nfv
    bnjwphm
    vi
    nfv
    bnjwpsm
    @4
    @13
    wcel
    @4
    @12
    cfv
    vy
    @2
    @12
    cfv
    @7
    ciun
    wceq
    wi
    #
    vi
    com
    wral
    vi
    bnj571.30
    @15
    vi
    com
    nfra1
    nfxfr
    nf3an
    nfxfr
    wet
    vi
    nfv
    nf3an
    @1
    @3
    @5
    @9
    @1
    @3
    @5
    wa
    #
    wa
    #
    @6
    cK
    @8
    @17
    @6
    cK
    wceq
    #
    wi
    @13
    @4
    @13
    @4
    wceq
    #
    @1
    @16
    @18
    @19
    @1
    @16
    w3a
    #
    @0
    wta
    wet
    wze
    w-bnj17
    #
    @18
    @21
    @1
    wze
    wa
    #
    @20
    @0
    wta
    wet
    wze
    df-bnj17
    @1
    @16
    @19
    w3a
    @1
    @16
    @19
    wa
    #
    wa
    @20
    @22
    @1
    @16
    @19
    3anass
    @19
    @1
    @16
    3anrot
    wze
    @23
    @1
    wze
    @3
    @5
    @19
    w3a
    @23
    bnj571.20
    @3
    @5
    @19
    df-3an
    bitri
    anbi2i
    3bitr4ri
    bitri
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
    bnj571.3
    bnj571.16
    bnj571.17
    bnj571.18
    bnj571.19
    bnj571.20
    bnj571.22
    bnj571.23
    bnj571.24
    bnj571.25
    bnj571.26
    bnj571.29
    bnj571.30
    bnj571.38
    bnj558
    sylbir
    3expib
    @13
    @4
    wne
    #
    @1
    @16
    @18
    @24
    @1
    @16
    w3a
    #
    @0
    wta
    wet
    wrh
    w-bnj17
    #
    @18
    @26
    @1
    wrh
    wa
    #
    @25
    @0
    wta
    wet
    wrh
    df-bnj17
    @1
    @16
    @24
    w3a
    @1
    @16
    @24
    wa
    #
    wa
    @25
    @27
    @1
    @16
    @24
    3anass
    @24
    @1
    @16
    3anrot
    wrh
    @28
    @1
    wrh
    @3
    @5
    @24
    w3a
    @28
    bnj571.21
    @3
    @5
    @24
    df-3an
    bitri
    anbi2i
    3bitr4ri
    bitri
    wta
    wet
    wrh
    vy
    cA
    vy
    vp
    cv
    @12
    cfv
    @7
    ciun
    cD
    cR
    vf
    vi
    vm
    vn
    cG
    cK
    vp
    bnjwphm
    bnjwpsm
    bnj571.3
    bnj571.17
    bnj571.19
    bnj571.21
    bnj571.24
    bnj571.16
    bnj571.40
    bnj571.30
    bnj570
    sylbir
    3expib
    pm2.61ine
    bnj571.24
    syl6eq
    exp32
    alrimi
    bnjwpsn
    @10
    vi
    com
    bnj571.33
    bnj946
    sylibr
end
