include "cdm.mm"
include "crn.mm"
include "cep.mm"
include "wiso.mm"
include "ordtypelem8.mm"
include "wceq.mm"
include "wb.mm"
include "cin.mm"
include "wf.mm"
include "wss.mm"
include "ordtypelem4.mm"
include "frn.mm"
include "syl.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "wrex.mm"
include "wral.mm"
include "cima.mm"
include "word.mm"
include "ordtypelem2.mm"
include "ordirr.mm"
include "con0.mm"
include "wlim.mm"
include "wfun.mm"
include "tfr1a.mm"
include "simpri.mm"
include "limord.mm"
include "ax-mp.mm"
include "cres.mm"
include "cvv.mm"
include "ordtypelem1.mm"
include "eqeltrrd.mm"
include "tfr2b.mm"
include "mpbird.mm"
include "ordelon.mm"
include "sylancr.mm"
include "imaeq2.mm"
include "raleqdv.mm"
include "rexbidv.mm"
include "crab.mm"
include "weq.mm"
include "breq1.mm"
include "cbvralv.mm"
include "breq2.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "cbvrexv.mm"
include "cbvrabv.mm"
include "eqtri.mm"
include "elrab2.mm"
include "baib.mm"
include "mtbid.mm"
include "ralnex.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "rneqd.mm"
include "df-ima.mm"
include "syl6eqr.mm"
include "adantr.mm"
include "wfn.mm"
include "ffun.mm"
include "funfn.mm"
include "sylib.mm"
include "ralrn.mm"
include "bitr3d.mm"
include "rexnal.mm"
include "ordtypelem7.mm"
include "ord.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "isoeq5.mm"
include "mpbid.mm"

theorem ordtypelem9
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cC: class C
  let cR: class R
  let cT: class T
  let vh: setvar h
  let vj: setvar j
  let cF: class F
  let cG: class G
  let cO: class O
  let vf: setvar f
  let vr: setvar r
  let vs: setvar s
  let va: setvar a
  let cM: class M
  let vb: setvar b
  let cN: class N
  let vc: setvar c
  let vi: setvar i
  let vm: setvar m
  let vy: setvar y
  assume ordtypelem.1: |- F = recs ( G )
  assume ordtypelem.2: |- C = { w e. A | A. j e. ran h j R w }
  assume ordtypelem.3: |- G = ( h e. _V |-> ( iota_ v e. C A. u e. C -. u R v ) )
  assume ordtypelem.5: |- T = { x e. On | E. t e. A A. z e. ( F " x ) z R t }
  assume ordtypelem.6: |- O = OrdIso ( R , A )
  assume ordtypelem.7: |- ( ph -> R We A )
  assume ordtypelem.8: |- ( ph -> R Se A )
  assume ordtypelem9.1: |- ( ph -> O e. _V )

  disjoint u v
  disjoint C u
  disjoint C v
  disjoint h j
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h z
  disjoint j t
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t z
  disjoint u w
  disjoint u x
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint w x
  disjoint w z
  disjoint x z
  disjoint R h
  disjoint R j
  disjoint R t
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R x
  disjoint R z
  disjoint A h
  disjoint A j
  disjoint A t
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint A z
  disjoint O t
  disjoint O u
  disjoint O v
  disjoint O x
  disjoint ph t
  disjoint ph x
  disjoint F h
  disjoint F j
  disjoint F t
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F z
  disjoint f r
  disjoint f s
  disjoint f u
  disjoint f v
  disjoint C f
  disjoint r s
  disjoint r u
  disjoint r v
  disjoint C r
  disjoint s u
  disjoint s v
  disjoint C s
  disjoint a h
  disjoint a j
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a z
  disjoint M a
  disjoint M h
  disjoint M j
  disjoint M t
  disjoint M u
  disjoint M v
  disjoint M w
  disjoint M x
  disjoint M z
  disjoint a b
  disjoint N a
  disjoint b j
  disjoint b u
  disjoint b w
  disjoint N b
  disjoint N j
  disjoint N u
  disjoint N w
  disjoint a c
  disjoint a f
  disjoint a i
  disjoint a m
  disjoint a r
  disjoint a s
  disjoint a y
  disjoint R a
  disjoint b c
  disjoint b f
  disjoint b h
  disjoint b i
  disjoint b m
  disjoint b r
  disjoint b s
  disjoint b t
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint R b
  disjoint c f
  disjoint c h
  disjoint c i
  disjoint c j
  disjoint c m
  disjoint c r
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint R c
  disjoint f h
  disjoint f i
  disjoint f j
  disjoint f m
  disjoint f t
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint R f
  disjoint h i
  disjoint h m
  disjoint h r
  disjoint h s
  disjoint h y
  disjoint i j
  disjoint i m
  disjoint i r
  disjoint i s
  disjoint i t
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint R i
  disjoint j m
  disjoint j r
  disjoint j s
  disjoint j y
  disjoint m r
  disjoint m s
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint R m
  disjoint r t
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint R r
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint R s
  disjoint t y
  disjoint u y
  disjoint v y
  disjoint w y
  disjoint x y
  disjoint y z
  disjoint R y
  disjoint T a
  disjoint T b
  disjoint T c
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A m
  disjoint A r
  disjoint A s
  disjoint A y
  disjoint O a
  disjoint O b
  disjoint O c
  disjoint O m
  disjoint a ph
  disjoint b ph
  disjoint m ph
  disjoint F a
  disjoint F b
  disjoint F c
  assert |- ( ph -> O Isom _E , R ( dom O , A ) )

  proof
    wph
    cO
    cdm
    #
    cO
    crn
    #
    cep
    cR
    cO
    wiso
    #
    @0
    cA
    cep
    cR
    cO
    wiso
    #
    wph
    vx
    vz
    vw
    vv
    vu
    vt
    cA
    cC
    cR
    cT
    vh
    vj
    cF
    cG
    cO
    ordtypelem.1
    ordtypelem.2
    ordtypelem.3
    ordtypelem.5
    ordtypelem.6
    ordtypelem.7
    ordtypelem.8
    ordtypelem8
    wph
    @1
    cA
    wceq
    @2
    @3
    wb
    wph
    @1
    cA
    wph
    cT
    cF
    cdm
    #
    cin
    #
    cA
    cO
    wf
    #
    @1
    cA
    wss
    wph
    vx
    vz
    vw
    vv
    vu
    vt
    cA
    cC
    cR
    cT
    vh
    vj
    cF
    cG
    cO
    ordtypelem.1
    ordtypelem.2
    ordtypelem.3
    ordtypelem.5
    ordtypelem.6
    ordtypelem.7
    ordtypelem.8
    ordtypelem4
    #
    @5
    cA
    cO
    frn
    syl
    wph
    vb
    cA
    @1
    wph
    vb
    cv
    #
    cA
    wcel
    #
    @8
    @1
    wcel
    #
    wph
    @9
    wa
    #
    vm
    cv
    #
    cO
    cfv
    #
    @8
    cR
    wbr
    #
    wn
    #
    vm
    @0
    wrex
    #
    @10
    @11
    @14
    vm
    @0
    wral
    #
    wn
    @16
    @11
    vc
    cv
    #
    @8
    cR
    wbr
    #
    vc
    cF
    cT
    cima
    #
    wral
    #
    @17
    wph
    @21
    wn
    #
    vb
    cA
    wph
    @21
    vb
    cA
    wrex
    #
    wn
    @22
    vb
    cA
    wral
    wph
    cT
    cT
    wcel
    #
    @23
    wph
    cT
    word
    #
    @24
    wn
    wph
    vx
    vz
    vw
    vv
    vu
    vt
    cA
    cC
    cR
    cT
    vh
    vj
    cF
    cG
    cO
    ordtypelem.1
    ordtypelem.2
    ordtypelem.3
    ordtypelem.5
    ordtypelem.6
    ordtypelem.7
    ordtypelem.8
    ordtypelem2
    #
    cT
    ordirr
    syl
    wph
    cT
    con0
    wcel
    #
    @24
    @23
    wb
    wph
    @4
    word
    #
    cT
    @4
    wcel
    #
    @27
    @4
    wlim
    #
    @28
    cF
    wfun
    @30
    cF
    cG
    ordtypelem.1
    tfr1a
    simpri
    @4
    limord
    ax-mp
    wph
    @29
    cF
    cT
    cres
    #
    cvv
    wcel
    #
    wph
    cO
    @31
    cvv
    wph
    vx
    vz
    vw
    vv
    vu
    vt
    cA
    cC
    cR
    cT
    vh
    vj
    cF
    cG
    cO
    ordtypelem.1
    ordtypelem.2
    ordtypelem.3
    ordtypelem.5
    ordtypelem.6
    ordtypelem.7
    ordtypelem.8
    ordtypelem1
    #
    ordtypelem9.1
    eqeltrrd
    wph
    @25
    @29
    @32
    wb
    @26
    cT
    cF
    cG
    ordtypelem.1
    tfr2b
    syl
    mpbird
    @4
    cT
    ordelon
    sylancr
    @24
    @27
    @23
    @19
    vc
    cF
    va
    cv
    #
    cima
    #
    wral
    #
    vb
    cA
    wrex
    #
    @23
    va
    cT
    con0
    cT
    @34
    cT
    wceq
    #
    @36
    @21
    vb
    cA
    @38
    @19
    vc
    @35
    @20
    @34
    cT
    cF
    imaeq2
    raleqdv
    rexbidv
    cT
    vz
    cv
    #
    vt
    cv
    #
    cR
    wbr
    #
    vz
    cF
    vx
    cv
    #
    cima
    #
    wral
    #
    vt
    cA
    wrex
    #
    vx
    con0
    crab
    @37
    va
    con0
    crab
    ordtypelem.5
    @45
    @37
    vx
    va
    con0
    @45
    @19
    vc
    @43
    wral
    #
    vb
    cA
    wrex
    vx
    va
    weq
    #
    @37
    @44
    @46
    vt
    vb
    cA
    @44
    @18
    @40
    cR
    wbr
    #
    vc
    @43
    wral
    vt
    vb
    weq
    #
    @46
    @41
    @48
    vz
    vc
    @43
    @39
    @18
    @40
    cR
    breq1
    cbvralv
    @49
    @48
    @19
    vc
    @43
    @40
    @8
    @18
    cR
    breq2
    ralbidv
    syl5bb
    cbvrexv
    @47
    @46
    @36
    vb
    cA
    @47
    @19
    vc
    @43
    @35
    @42
    @34
    cF
    imaeq2
    raleqdv
    rexbidv
    syl5bb
    cbvrabv
    eqtri
    elrab2
    baib
    syl
    mtbid
    @21
    vb
    cA
    ralnex
    sylibr
    r19.21bi
    @11
    @19
    vc
    @1
    wral
    #
    @21
    @17
    @11
    @19
    vc
    @1
    @20
    wph
    @1
    @20
    wceq
    @9
    wph
    @1
    @31
    crn
    @20
    wph
    cO
    @31
    @33
    rneqd
    cF
    cT
    df-ima
    syl6eqr
    adantr
    raleqdv
    @11
    cO
    @0
    wfn
    #
    @50
    @17
    wb
    wph
    @51
    @9
    wph
    cO
    wfun
    #
    @51
    wph
    @6
    @52
    @7
    @5
    cA
    cO
    ffun
    syl
    cO
    funfn
    sylib
    adantr
    @19
    @14
    vc
    vm
    @0
    cO
    @18
    @13
    @8
    cR
    breq1
    ralrn
    syl
    bitr3d
    mtbid
    @14
    vm
    @0
    rexnal
    sylibr
    @11
    @15
    @10
    vm
    @0
    @11
    @12
    @0
    wcel
    wa
    @14
    @10
    wph
    vx
    vz
    vw
    vv
    vu
    vt
    cA
    cC
    cR
    cT
    vh
    vj
    cF
    cG
    @12
    @8
    cO
    ordtypelem.1
    ordtypelem.2
    ordtypelem.3
    ordtypelem.5
    ordtypelem.6
    ordtypelem.7
    ordtypelem.8
    ordtypelem7
    ord
    rexlimdva
    mpd
    ex
    ssrdv
    eqssd
    @0
    @1
    cA
    cep
    cR
    cO
    isoeq5
    syl
    mpbid
end
