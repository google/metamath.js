include "w-bnj15.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wfn.mm"
include "w3a.mm"
include "wi.mm"
include "c0.mm"
include "c-bnj14.mm"
include "cop.mm"
include "csn.mm"
include "cfv.mm"
include "wceq.mm"
include "csuc.mm"
include "c1o.mm"
include "ciun.mm"
include "com.mm"
include "wral.mm"
include "wsbc.mm"
include "wex.mm"
include "wmo.mm"
include "biid.mm"
include "bnj118.mm"
include "bicomi.mm"
include "bnj105.mm"
include "bnj92.mm"
include "bnj121.mm"
include "anbi2i.mm"
include "anbi12i.mm"
include "df-3an.mm"
include "3bitr4i.mm"
include "imbi2i.mm"
include "bitri.mm"
include "eqid.mm"
include "sbcbii.mm"
include "bnj124.mm"
include "bnj125.mm"
include "bnj126.mm"
include "bitr2i.mm"
include "bnj156.mm"
include "bnj154.mm"
include "bnj155.mm"
include "bitr3i.mm"
include "bnj151.mm"

theorem bnj153
  let wph: wff ph
  let wps: wff ps
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let vg: setvar g
  assume bnj153.1: |- ( ph <-> ( f ` (/) ) = _pred ( x , A , R ) )
  assume bnj153.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj153.3: |- D = ( _om \ { (/) } )
  assume bnj153.4: |- ( th <-> ( ( R _FrSe A /\ x e. A ) -> E! f ( f Fn n /\ ph /\ ps ) ) )
  assume bnj153.5: |- ( ta <-> A. m e. D ( m _E n -> [. m / n ]. th ) )

  disjoint A f
  disjoint A i
  disjoint A x
  disjoint A y
  disjoint f i
  disjoint f x
  disjoint f y
  disjoint i x
  disjoint i y
  disjoint x y
  disjoint A n
  disjoint f n
  disjoint i n
  disjoint n x
  disjoint n y
  disjoint R f
  disjoint R i
  disjoint R x
  disjoint R y
  disjoint R n
  disjoint m n
  disjoint A g
  disjoint f g
  disjoint g i
  disjoint g x
  disjoint g y
  disjoint R g
  assert |- ( n = 1o -> ( ( n e. D /\ ta ) -> th ) )

  proof
    wph
    wps
    wth
    wta
    cA
    cR
    w-bnj15
    vx
    cv
    #
    cA
    wcel
    wa
    #
    vf
    cv
    #
    vn
    cv
    wfn
    wph
    wps
    w3a
    wi
    #
    vx
    vy
    cA
    cD
    cR
    vf
    vg
    vi
    vm
    vn
    c0
    cA
    cR
    @0
    c-bnj14
    #
    cop
    csn
    #
    c0
    @2
    cfv
    @4
    wceq
    #
    vi
    cv
    #
    csuc
    #
    c1o
    wcel
    #
    @8
    @2
    cfv
    vy
    @7
    @2
    cfv
    cA
    cR
    vy
    cv
    c-bnj14
    #
    ciun
    wceq
    wi
    vi
    com
    wral
    #
    wth
    vn
    c1o
    wsbc
    #
    @1
    @2
    c1o
    wfn
    #
    @6
    @11
    w3a
    #
    wi
    #
    @6
    vf
    @5
    wsbc
    #
    @11
    vf
    @5
    wsbc
    #
    @1
    @5
    c1o
    wfn
    #
    c0
    @5
    cfv
    @4
    wceq
    #
    @9
    @8
    @5
    cfv
    vy
    @7
    @5
    cfv
    @10
    ciun
    wceq
    wi
    vi
    com
    wral
    #
    w3a
    #
    wi
    #
    @1
    @14
    vf
    wex
    wi
    #
    @14
    @6
    vf
    vg
    cv
    #
    wsbc
    #
    @11
    vf
    @24
    wsbc
    #
    @1
    @14
    vf
    wmo
    wi
    #
    @24
    c1o
    wfn
    #
    c0
    @24
    cfv
    @4
    wceq
    #
    @9
    @8
    @24
    cfv
    vy
    @7
    @24
    cfv
    @10
    ciun
    wceq
    wi
    vi
    com
    wral
    #
    w3a
    #
    bnj153.1
    bnj153.2
    bnj153.3
    bnj153.4
    bnj153.5
    @3
    biid
    #
    wph
    vn
    c1o
    wsbc
    #
    @6
    wph
    vx
    cA
    cR
    vf
    vn
    @33
    bnj153.1
    @33
    biid
    #
    bnj118
    #
    bicomi
    wps
    vn
    c1o
    wsbc
    #
    @11
    wps
    vy
    cA
    cR
    vf
    vi
    vn
    c1o
    bnj153.2
    bnj105
    bnj92
    #
    bicomi
    @12
    biid
    @23
    biid
    @27
    biid
    @3
    vn
    c1o
    wsbc
    #
    @15
    @38
    @1
    @13
    @33
    @36
    w3a
    #
    wi
    @15
    wph
    wps
    @3
    vx
    cA
    cR
    vf
    vn
    @33
    @36
    @38
    @32
    @38
    biid
    @34
    @36
    biid
    #
    bnj121
    #
    @39
    @14
    @1
    @13
    @33
    wa
    #
    @36
    wa
    @13
    @6
    wa
    #
    @11
    wa
    @39
    @14
    @42
    @43
    @36
    @11
    @33
    @6
    @13
    @35
    anbi2i
    @37
    anbi12i
    @13
    @33
    @36
    df-3an
    @13
    @6
    @11
    df-3an
    3bitr4i
    #
    imbi2i
    bitri
    bicomi
    #
    @5
    eqid
    #
    @16
    biid
    @17
    biid
    @15
    vf
    @5
    wsbc
    @38
    vf
    @5
    wsbc
    #
    @22
    @15
    @38
    vf
    @5
    @45
    sbcbii
    @47
    @1
    @18
    @33
    vf
    @5
    wsbc
    #
    @36
    vf
    @5
    wsbc
    #
    w3a
    #
    wi
    @22
    vx
    cA
    cR
    vf
    @5
    @33
    @36
    @38
    @48
    @49
    @47
    @46
    @48
    biid
    #
    @49
    biid
    #
    @47
    biid
    @41
    bnj124
    @50
    @21
    @1
    @18
    @48
    wa
    #
    @49
    wa
    @18
    @19
    wa
    #
    @20
    wa
    @50
    @21
    @53
    @54
    @49
    @20
    @48
    @19
    @18
    wph
    vx
    cA
    cR
    vf
    vn
    @5
    @33
    @48
    bnj153.1
    @34
    @51
    @46
    bnj125
    anbi2i
    wps
    vx
    vy
    cA
    cR
    vf
    vi
    vn
    @5
    @36
    @49
    bnj153.2
    @40
    @52
    @46
    bnj126
    anbi12i
    @18
    @48
    @49
    df-3an
    @18
    @19
    @20
    df-3an
    3bitr4i
    imbi2i
    bitri
    bitr2i
    @14
    biid
    @31
    @39
    vf
    @24
    wsbc
    #
    @14
    vf
    @24
    wsbc
    @55
    @28
    @33
    vf
    @24
    wsbc
    #
    @36
    vf
    @24
    wsbc
    #
    w3a
    #
    @31
    vf
    vg
    @33
    @36
    @39
    @56
    @57
    @55
    @39
    biid
    @55
    biid
    @56
    biid
    #
    @57
    biid
    #
    bnj156
    @28
    @56
    wa
    #
    @57
    wa
    @28
    @29
    wa
    #
    @30
    wa
    @58
    @31
    @61
    @62
    @57
    @30
    @56
    @29
    @28
    vx
    cA
    cR
    vf
    vg
    @33
    @56
    @59
    @35
    bnj154
    anbi2i
    vy
    cA
    cR
    vf
    vg
    vi
    @36
    @57
    @60
    @36
    @36
    @11
    @40
    @37
    bitri
    bnj155
    anbi12i
    @28
    @56
    @57
    df-3an
    @28
    @29
    @30
    df-3an
    3bitr4i
    bitri
    @39
    @14
    vf
    @24
    @44
    sbcbii
    bitr3i
    @25
    biid
    @26
    biid
    bnj151
end
