include "cv.mm"
include "c1o.mm"
include "wne.mm"
include "wcel.mm"
include "w-bnj15.mm"
include "wa.mm"
include "wfn.mm"
include "w3a.mm"
include "wex.mm"
include "wi.mm"
include "anim1i.mm"
include "nfv.mm"
include "19.41.mm"
include "exbii.mm"
include "cep.mm"
include "wbr.mm"
include "wsbc.mm"
include "bnj1095.mm"
include "nf5i.mm"
include "bitr2i.mm"
include "sylib.mm"
include "csuc.mm"
include "wceq.mm"
include "com.mm"
include "bnj1232.mm"
include "bnj219.mm"
include "bnj770.mm"
include "jca.mm"
include "bnj170.mm"
include "sylibr.mm"
include "syl.mm"
include "simpl.mm"
include "2eximi.mm"
include "weu.mm"
include "biimpi.mm"
include "euex.mm"
include "syl6.mm"
include "impcom.mm"
include "bnj1198.mm"
include "adantrr.mm"
include "id.mm"
include "3com23.mm"
include "3expia.mm"
include "eximdv.mm"
include "ad2ant2rl.mm"
include "mpd.mm"
include "3jca.mm"
include "eximi.mm"
include "nfe1.mm"
include "cvv.mm"
include "nfcv.mm"
include "nfsbc1v.mm"
include "nfxfr.mm"
include "nf3an.mm"
include "fneq1.mm"
include "sbceq1a.mm"
include "syl6bbr.mm"
include "3anbi123d.mm"
include "spcegf.mm"
include "ax-mp.mm"
include "c0.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "bnj154.mm"
include "bnj526.mm"
include "bitr4i.mm"
include "ciun.mm"
include "wral.mm"
include "vex.mm"
include "bnj540.mm"
include "anbi12i.mm"
include "anbi2i.mm"
include "3anass.mm"
include "3bitr4i.mm"
include "weq.mm"
include "cbvex.mm"
include "3imtr4i.mm"
include "exlimi.mm"
include "3syl.mm"
include "expcom.mm"
include "exlimivv.mm"
include "3impa.mm"

theorem bnj607
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vh: setvar h
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let vp: setvar p
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwchm: wff ch'
  let bnjwphn: wff ph"
  let bnjwpsn: wff ps"
  let bnjwph0: wff ph0
  let bnjwps0: wff ps0
  let bnjwph1: wff ph1
  let bnjwps1: wff ps1
  assume bnj607.5: |- ( th <-> A. m e. D ( m _E n -> [. m / n ]. ch ) )
  assume bnj607.13: |- ( ph" <-> [. G / f ]. ph )
  assume bnj607.14: |- ( ps" <-> [. G / f ]. ps )
  assume bnj607.17: |- ( ta <-> ( f Fn m /\ ph' /\ ps' ) )
  assume bnj607.19: |- ( et <-> ( m e. D /\ n = suc m /\ p e. _om /\ m = suc p ) )
  assume bnj607.28: |- G e. _V
  assume bnj607.31: |- ( ch' <-> ( ( R _FrSe A /\ x e. A ) -> E! f ( f Fn m /\ ph' /\ ps' ) ) )
  assume bnj607.32: |- ( ph" <-> ( G ` (/) ) = _pred ( x , A , R ) )
  assume bnj607.33: |- ( ps" <-> A. i e. _om ( suc i e. n -> ( G ` suc i ) = U_ y e. ( G ` i ) _pred ( y , A , R ) ) )
  assume bnj607.37: |- ( ( n =/= 1o /\ n e. D ) -> E. m E. p et )
  assume bnj607.38: |- ( ( th /\ m e. D /\ m _E n ) -> ch' )
  assume bnj607.41: |- ( ( R _FrSe A /\ ta /\ et ) -> G Fn n )
  assume bnj607.42: |- ( ( R _FrSe A /\ ta /\ et ) -> ph" )
  assume bnj607.43: |- ( ( R _FrSe A /\ ta /\ et ) -> ps" )
  assume bnj607.1: |- ( ph <-> ( f ` (/) ) = _pred ( x , A , R ) )
  assume bnj607.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj607.400: |- ( ph0 <-> [. h / f ]. ph )
  assume bnj607.401: |- ( ps0 <-> [. h / f ]. ps )
  assume bnj607.300: |- ( ph1 <-> [. G / h ]. ph0 )
  assume bnj607.301: |- ( ps1 <-> [. G / h ]. ps0 )

  disjoint A f
  disjoint A h
  disjoint f h
  disjoint A m
  disjoint f m
  disjoint A p
  disjoint f p
  disjoint G h
  disjoint G i
  disjoint G y
  disjoint h i
  disjoint h y
  disjoint i y
  disjoint R f
  disjoint R h
  disjoint R m
  disjoint R p
  disjoint et f
  disjoint f i
  disjoint f y
  disjoint f n
  disjoint h n
  disjoint f x
  disjoint h x
  disjoint h ph
  disjoint h ps
  disjoint m n
  disjoint m ph
  disjoint m ps
  disjoint m x
  disjoint n p
  disjoint p ph
  disjoint p ps
  disjoint p th
  disjoint p x
  assert |- ( ( n =/= 1o /\ n e. D /\ th ) -> ( ( R _FrSe A /\ x e. A ) -> E. f ( f Fn n /\ ph /\ ps ) ) )

  proof
    vn
    cv
    #
    c1o
    wne
    #
    @0
    cD
    wcel
    #
    wth
    cA
    cR
    w-bnj15
    #
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    vf
    cv
    #
    @0
    wfn
    #
    wph
    wps
    w3a
    #
    vf
    wex
    #
    wi
    #
    @1
    @2
    wa
    #
    wth
    wa
    #
    wet
    wth
    wa
    #
    vp
    wex
    #
    vm
    wex
    #
    bnjwchm
    wet
    wa
    #
    vp
    wex
    vm
    wex
    @11
    @13
    wet
    vp
    wex
    #
    vm
    wex
    #
    wth
    wa
    #
    @16
    @12
    @19
    wth
    bnj607.37
    anim1i
    @16
    @18
    wth
    wa
    #
    vm
    wex
    @20
    @15
    @21
    vm
    wet
    wth
    vp
    wth
    vp
    nfv
    19.41
    exbii
    @18
    wth
    vm
    wth
    vm
    wth
    vm
    cv
    #
    @0
    cep
    wbr
    #
    wch
    vn
    @22
    wsbc
    wi
    vm
    cD
    bnj607.5
    bnj1095
    nf5i
    19.41
    bitr2i
    sylib
    @14
    @17
    vm
    vp
    @14
    bnjwchm
    wet
    @14
    wth
    @22
    cD
    wcel
    #
    @23
    w3a
    #
    bnjwchm
    @14
    @24
    @23
    wa
    #
    wth
    wa
    @25
    wet
    @26
    wth
    wet
    @24
    @23
    wet
    @24
    @0
    @22
    csuc
    wceq
    #
    vp
    cv
    #
    com
    wcel
    #
    @22
    @28
    csuc
    wceq
    #
    bnj607.19
    bnj1232
    @24
    @27
    @29
    @30
    @23
    wet
    bnj607.19
    vm
    vn
    bnj219
    bnj770
    jca
    anim1i
    wth
    @24
    @23
    bnj170
    sylibr
    bnj607.38
    syl
    wet
    wth
    simpl
    jca
    2eximi
    @17
    @11
    vm
    vp
    @6
    @17
    @10
    @6
    @17
    wa
    #
    @3
    wta
    wet
    w3a
    #
    vf
    wex
    #
    cG
    @0
    wfn
    #
    bnjwphn
    bnjwpsn
    w3a
    #
    vf
    wex
    @10
    @31
    wta
    vf
    wex
    #
    @33
    @6
    bnjwchm
    @36
    wet
    @6
    bnjwchm
    wa
    @7
    @22
    wfn
    bnjwphm
    bnjwpsm
    w3a
    #
    vf
    wta
    bnjwchm
    @6
    @37
    vf
    wex
    #
    bnjwchm
    @6
    @37
    vf
    weu
    #
    @38
    bnjwchm
    @6
    @39
    wi
    bnj607.31
    biimpi
    @37
    vf
    euex
    syl6
    impcom
    bnj607.17
    bnj1198
    adantrr
    @3
    wet
    @36
    @33
    wi
    @5
    bnjwchm
    @3
    wet
    wa
    wta
    @32
    vf
    @3
    wet
    wta
    @32
    @3
    wta
    wet
    @32
    @32
    id
    3com23
    3expia
    eximdv
    ad2ant2rl
    mpd
    @32
    @35
    vf
    @32
    @34
    bnjwphn
    bnjwpsn
    bnj607.41
    bnj607.42
    bnj607.43
    3jca
    eximi
    @35
    @10
    vf
    @9
    vf
    nfe1
    @34
    bnjwph1
    bnjwps1
    w3a
    #
    vh
    cv
    #
    @0
    wfn
    #
    bnjwph0
    bnjwps0
    w3a
    #
    vh
    wex
    #
    @35
    @10
    cG
    cvv
    wcel
    @40
    @44
    wi
    bnj607.28
    @43
    @40
    vh
    cG
    cvv
    vh
    cG
    nfcv
    @34
    bnjwph1
    bnjwps1
    vh
    @34
    vh
    nfv
    bnjwph1
    bnjwph0
    vh
    cG
    wsbc
    #
    vh
    bnj607.300
    bnjwph0
    vh
    cG
    nfsbc1v
    nfxfr
    bnjwps1
    bnjwps0
    vh
    cG
    wsbc
    #
    vh
    bnj607.301
    bnjwps0
    vh
    cG
    nfsbc1v
    nfxfr
    nf3an
    @41
    cG
    wceq
    #
    @42
    @34
    bnjwph0
    bnjwph1
    bnjwps0
    bnjwps1
    @0
    @41
    cG
    fneq1
    @47
    bnjwph0
    @45
    bnjwph1
    bnjwph0
    vh
    cG
    sbceq1a
    bnj607.300
    syl6bbr
    @47
    bnjwps0
    @46
    bnjwps1
    bnjwps0
    vh
    cG
    sbceq1a
    bnj607.301
    syl6bbr
    3anbi123d
    spcegf
    ax-mp
    @34
    bnjwphn
    bnjwpsn
    wa
    #
    wa
    @34
    bnjwph1
    bnjwps1
    wa
    #
    wa
    @35
    @40
    @48
    @49
    @34
    bnjwphn
    bnjwph1
    bnjwpsn
    bnjwps1
    bnjwphn
    c0
    cG
    cfv
    cA
    cR
    @4
    c-bnj14
    wceq
    bnjwph1
    bnj607.32
    bnjwph0
    cA
    cR
    vh
    cG
    @4
    bnjwph1
    vx
    cA
    cR
    vf
    vh
    wph
    bnjwph0
    bnj607.400
    bnj607.1
    bnj154
    bnj607.300
    bnj607.28
    bnj526
    bitr4i
    bnjwpsn
    vi
    cv
    #
    csuc
    #
    @0
    wcel
    @51
    cG
    cfv
    vy
    @50
    cG
    cfv
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
    bnjwps1
    bnj607.33
    bnjwps0
    vy
    cA
    cR
    vh
    vi
    cG
    @0
    bnjwps1
    wps
    vy
    cA
    cR
    vf
    vi
    @41
    @0
    bnjwps0
    bnj607.2
    bnj607.401
    vh
    vex
    bnj540
    bnj607.301
    bnj607.28
    bnj540
    bitr4i
    anbi12i
    anbi2i
    @34
    bnjwphn
    bnjwpsn
    3anass
    @34
    bnjwph1
    bnjwps1
    3anass
    3bitr4i
    @9
    @43
    vf
    vh
    @9
    vh
    nfv
    @42
    bnjwph0
    bnjwps0
    vf
    @42
    vf
    nfv
    bnjwph0
    wph
    vf
    @41
    wsbc
    #
    vf
    bnj607.400
    wph
    vf
    @41
    nfsbc1v
    nfxfr
    bnjwps0
    wps
    vf
    @41
    wsbc
    #
    vf
    bnj607.401
    wps
    vf
    @41
    nfsbc1v
    nfxfr
    nf3an
    vf
    vh
    weq
    #
    @8
    @42
    wph
    bnjwph0
    wps
    bnjwps0
    @0
    @7
    @41
    fneq1
    @54
    wph
    @52
    bnjwph0
    wph
    vf
    @41
    sbceq1a
    bnj607.400
    syl6bbr
    @54
    wps
    @53
    bnjwps0
    wps
    vf
    @41
    sbceq1a
    bnj607.401
    syl6bbr
    3anbi123d
    cbvex
    3imtr4i
    exlimi
    3syl
    expcom
    exlimivv
    3syl
    3impa
end
