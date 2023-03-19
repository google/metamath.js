include "w3a.mm"
include "wi.mm"
include "wex.mm"
include "wa.mm"
include "wel.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "w-bnj15.mm"
include "c-bnj18.mm"
include "c-bnj14.mm"
include "bnj917.mm"
include "bnj771.mm"
include "3anass.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "3exbii.mm"
include "sylib.mm"
include "bnj986.mm"
include "ancli.mm"
include "19.42vv.mm"
include "sylibr.mm"
include "anim1i.mm"
include "19.41vv.mm"
include "df-3an.mm"
include "2exbii.mm"
include "2eximi.mm"
include "bnj593.mm"
include "19.37v.mm"
include "exbii.mm"
include "bnj132.mm"
include "mpbir.mm"

theorem bnj996
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cX: class X
  let vp: setvar p
  assume bnj996.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj996.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj996.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj996.4: |- ( th <-> ( R _FrSe A /\ X e. A /\ y e. _trCl ( X , A , R ) /\ z e. _pred ( y , A , R ) ) )
  assume bnj996.5: |- ( ta <-> ( m e. _om /\ n = suc m /\ p = suc n ) )
  assume bnj996.6: |- ( et <-> ( i e. n /\ y e. ( f ` i ) ) )
  assume bnj996.13: |- D = ( _om \ { (/) } )
  assume bnj996.14: |- B = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }

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
  disjoint D i
  disjoint R f
  disjoint R i
  disjoint R n
  disjoint R y
  disjoint X f
  disjoint X i
  disjoint X n
  disjoint X y
  disjoint ch m
  disjoint ch p
  disjoint m p
  disjoint et m
  disjoint et p
  disjoint f th
  disjoint i th
  disjoint n th
  disjoint i ph
  disjoint m n
  disjoint m th
  disjoint n p
  disjoint p th
  assert |- E. f E. n E. i E. m E. p ( th -> ( ch /\ ta /\ et ) )

  proof
    wth
    wch
    wta
    wet
    w3a
    #
    wi
    vp
    wex
    #
    vm
    wex
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
    wth
    @0
    vp
    wex
    #
    vm
    wex
    #
    vi
    wex
    #
    vn
    wex
    #
    vf
    wex
    wi
    wth
    wch
    wet
    wa
    #
    vi
    wex
    vn
    wex
    #
    @9
    vf
    wth
    wch
    vi
    vn
    wel
    #
    vy
    cv
    #
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
    vn
    wex
    vf
    wex
    #
    @11
    vf
    wex
    cA
    cR
    w-bnj15
    cX
    cA
    wcel
    @13
    cA
    cR
    cX
    c-bnj18
    wcel
    vz
    cv
    cA
    cR
    @13
    c-bnj14
    wcel
    @16
    wth
    bnj996.4
    wph
    wps
    wch
    vy
    cA
    cB
    cD
    cR
    vf
    vi
    vn
    cX
    bnj996.1
    bnj996.2
    bnj996.13
    bnj996.14
    bnj996.3
    bnj917
    bnj771
    @15
    @10
    vf
    vn
    vi
    @15
    wch
    @12
    @14
    wa
    #
    wa
    @10
    wch
    @12
    @14
    3anass
    wet
    @17
    wch
    bnj996.6
    anbi2i
    bitr4i
    3exbii
    sylib
    @10
    @7
    vn
    vi
    @10
    wch
    wta
    wa
    #
    wet
    wa
    #
    vp
    wex
    vm
    wex
    #
    @7
    @10
    @18
    vp
    wex
    vm
    wex
    #
    wet
    wa
    @20
    wch
    @21
    wet
    wch
    wch
    wta
    vp
    wex
    vm
    wex
    #
    wa
    @21
    wch
    @22
    wph
    wps
    wch
    wta
    cD
    vf
    vm
    vn
    vp
    bnj996.3
    bnj996.13
    bnj996.5
    bnj986
    ancli
    wch
    wta
    vm
    vp
    19.42vv
    sylibr
    anim1i
    @18
    wet
    vm
    vp
    19.41vv
    sylibr
    @0
    @19
    vm
    vp
    wch
    wta
    wet
    df-3an
    2exbii
    sylibr
    2eximi
    bnj593
    @5
    wth
    @9
    vf
    @4
    wth
    @9
    wi
    vf
    @4
    wth
    @8
    vn
    @3
    wth
    @8
    wi
    vn
    @3
    wth
    @7
    vi
    @2
    wth
    @7
    wi
    vi
    @2
    wth
    @6
    vm
    @1
    wth
    @6
    wi
    vm
    wth
    @0
    vp
    19.37v
    exbii
    bnj132
    exbii
    bnj132
    exbii
    bnj132
    exbii
    bnj132
    mpbir
end
