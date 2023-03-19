include "c-bnj18.mm"
include "cv.mm"
include "wfn.mm"
include "c0.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "wceq.mm"
include "csuc.mm"
include "wcel.mm"
include "ciun.mm"
include "wi.mm"
include "com.mm"
include "wral.mm"
include "w3a.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "cab.mm"
include "cdm.mm"
include "df-bnj18.mm"
include "df-iun.mm"
include "wa.mm"
include "anbi12i.mm"
include "anbi2i.mm"
include "3anass.mm"
include "3bitr4i.mm"
include "rexeqbii.mm"
include "abbii.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "anbi1i.mm"
include "rexbii2.mm"
include "eqtr4i.mm"

theorem bnj882
  let wph: wff ph
  let wps: wff ps
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let cX: class X
  let vw: setvar w
  assume bnj882.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj882.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj882.3: |- D = ( _om \ { (/) } )
  assume bnj882.4: |- B = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }

  disjoint A f
  disjoint A i
  disjoint A n
  disjoint A y
  disjoint f i
  disjoint f n
  disjoint f y
  disjoint i n
  disjoint i y
  disjoint n y
  disjoint R f
  disjoint R i
  disjoint R n
  disjoint R y
  disjoint X f
  disjoint X i
  disjoint X n
  disjoint X y
  disjoint A w
  disjoint f w
  disjoint i w
  disjoint n w
  disjoint w y
  disjoint R w
  disjoint X w
  disjoint B w
  assert |- _trCl ( X , A , R ) = U_ f e. B U_ i e. dom f ( f ` i )

  proof
    cA
    cR
    cX
    c-bnj18
    vf
    vf
    cv
    #
    vn
    cv
    #
    wfn
    #
    c0
    @0
    cfv
    cA
    cR
    cX
    c-bnj14
    wceq
    #
    vi
    cv
    #
    csuc
    #
    @1
    wcel
    @5
    @0
    cfv
    vy
    @4
    @0
    cfv
    #
    cA
    cR
    vy
    cv
    c-bnj14
    ciun
    wceq
    wi
    vi
    com
    wral
    #
    w3a
    #
    vn
    com
    c0
    csn
    cdif
    #
    wrex
    #
    vf
    cab
    #
    vi
    @0
    cdm
    @6
    ciun
    #
    ciun
    #
    vf
    cB
    @12
    ciun
    #
    vy
    cA
    cR
    vf
    vi
    vn
    cX
    df-bnj18
    @14
    vw
    cv
    @12
    wcel
    #
    vf
    cB
    wrex
    #
    vw
    cab
    #
    @13
    vf
    vw
    cB
    @12
    df-iun
    @13
    @15
    vf
    @11
    wrex
    #
    vw
    cab
    @17
    vf
    vw
    @11
    @12
    df-iun
    @16
    @18
    vw
    @15
    @15
    vf
    cB
    @11
    @0
    cB
    wcel
    @0
    @11
    wcel
    @15
    cB
    @11
    @0
    cB
    @2
    wph
    wps
    w3a
    #
    vn
    cD
    wrex
    #
    vf
    cab
    @11
    bnj882.4
    @20
    @10
    vf
    @19
    @8
    vn
    cD
    @9
    bnj882.3
    @2
    wph
    wps
    wa
    #
    wa
    @2
    @3
    @7
    wa
    #
    wa
    @19
    @8
    @21
    @22
    @2
    wph
    @3
    wps
    @7
    bnj882.1
    bnj882.2
    anbi12i
    anbi2i
    @2
    wph
    wps
    3anass
    @2
    @3
    @7
    3anass
    3bitr4i
    rexeqbii
    abbii
    eqtri
    eleq2i
    anbi1i
    rexbii2
    abbii
    eqtr4i
    eqtr4i
    eqtr4i
end
