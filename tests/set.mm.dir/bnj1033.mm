include "wa.mm"
include "c-bnj18.mm"
include "cv.mm"
include "wcel.mm"
include "wel.mm"
include "cfv.mm"
include "w3a.mm"
include "wex.mm"
include "bnj983.mm"
include "19.42v.mm"
include "df-3an.mm"
include "exbii.mm"
include "3bitr4i.mm"
include "bitri.mm"
include "w-bnj17.mm"
include "bnj255.mm"
include "anbi2i.mm"
include "3anass.mm"
include "bitr4i.mm"
include "3anbi3i.mm"
include "3exbii.mm"
include "sylbir.mm"
include "syl3an3b.mm"
include "3expia.mm"
include "ssrdv.mm"

theorem bnj1033
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let cK: class K
  let cX: class X
  assume bnj1033.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj1033.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj1033.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj1033.4: |- ( th <-> ( R _FrSe A /\ X e. A ) )
  assume bnj1033.5: |- ( ta <-> ( B e. _V /\ _TrFo ( B , A , R ) /\ _pred ( X , A , R ) C_ B ) )
  assume bnj1033.6: |- ( et <-> z e. _trCl ( X , A , R ) )
  assume bnj1033.7: |- ( ze <-> ( i e. n /\ z e. ( f ` i ) ) )
  assume bnj1033.8: |- D = ( _om \ { (/) } )
  assume bnj1033.9: |- K = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }
  assume bnj1033.10: |- ( E. f E. n E. i ( th /\ ta /\ ch /\ ze ) -> z e. B )

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
  disjoint A z
  disjoint f z
  disjoint i z
  disjoint n z
  disjoint B z
  disjoint D i
  disjoint R f
  disjoint R i
  disjoint R n
  disjoint R y
  disjoint R z
  disjoint X f
  disjoint X i
  disjoint X n
  disjoint X y
  disjoint X z
  disjoint f ta
  disjoint i ta
  disjoint n ta
  disjoint ta z
  disjoint f th
  disjoint i th
  disjoint n th
  disjoint th z
  disjoint i ph
  assert |- ( ( th /\ ta ) -> _trCl ( X , A , R ) C_ B )

  proof
    wth
    wta
    wa
    #
    vz
    cA
    cR
    cX
    c-bnj18
    #
    cB
    wth
    wta
    vz
    cv
    #
    @1
    wcel
    #
    @2
    cB
    wcel
    #
    @3
    wth
    wta
    wch
    vi
    vn
    wel
    #
    @2
    vi
    cv
    vf
    cv
    cfv
    wcel
    #
    w3a
    #
    vi
    wex
    #
    vn
    wex
    #
    vf
    wex
    #
    @4
    wph
    wps
    wch
    vy
    cA
    cK
    cD
    cR
    vf
    vi
    vn
    cX
    @2
    bnj1033.1
    bnj1033.2
    bnj1033.8
    bnj1033.9
    bnj1033.3
    bnj983
    wth
    wta
    @10
    w3a
    #
    wth
    wta
    @7
    w3a
    #
    vi
    wex
    #
    vn
    wex
    #
    vf
    wex
    #
    @4
    @15
    wth
    wta
    @9
    w3a
    #
    vf
    wex
    #
    @11
    @14
    @16
    vf
    @14
    wth
    wta
    @8
    w3a
    #
    vn
    wex
    #
    @16
    @13
    @18
    vn
    @0
    @7
    wa
    #
    vi
    wex
    @0
    @8
    wa
    #
    @13
    @18
    @0
    @7
    vi
    19.42v
    @12
    @20
    vi
    wth
    wta
    @7
    df-3an
    exbii
    wth
    wta
    @8
    df-3an
    #
    3bitr4i
    exbii
    @21
    vn
    wex
    @0
    @9
    wa
    #
    @19
    @16
    @0
    @8
    vn
    19.42v
    @18
    @21
    vn
    @22
    exbii
    wth
    wta
    @9
    df-3an
    #
    3bitr4i
    bitri
    exbii
    @23
    vf
    wex
    @0
    @10
    wa
    @17
    @11
    @0
    @9
    vf
    19.42v
    @16
    @23
    vf
    @24
    exbii
    wth
    wta
    @10
    df-3an
    3bitr4i
    bitri
    @15
    wth
    wta
    wch
    wze
    w-bnj17
    #
    vi
    wex
    vn
    wex
    vf
    wex
    @4
    @25
    @12
    vf
    vn
    vi
    @25
    wth
    wta
    wch
    wze
    wa
    #
    w3a
    @12
    wth
    wta
    wch
    wze
    bnj255
    @26
    @7
    wth
    wta
    @26
    wch
    @5
    @6
    wa
    #
    wa
    @7
    wze
    @27
    wch
    bnj1033.7
    anbi2i
    wch
    @5
    @6
    3anass
    bitr4i
    3anbi3i
    bitri
    3exbii
    bnj1033.10
    sylbir
    sylbir
    syl3an3b
    3expia
    ssrdv
end
