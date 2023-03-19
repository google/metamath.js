include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "crn.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "cdif.mm"
include "eldif.mm"
include "con0.mm"
include "cin.mm"
include "wf.mm"
include "wceq.mm"
include "ordtypelem4.mm"
include "adantr.mm"
include "fdm.mm"
include "syl.mm"
include "inss1.mm"
include "word.mm"
include "wss.mm"
include "ordtypelem2.mm"
include "ordsson.mm"
include "syl5ss.mm"
include "eqsstrd.mm"
include "sseld.mm"
include "cv.mm"
include "eleq1.mm"
include "fveq2.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "wral.mm"
include "r19.21v.mm"
include "wb.mm"
include "wlim.mm"
include "wfun.mm"
include "tfr1a.mm"
include "simpri.mm"
include "limord.mm"
include "ax-mp.mm"
include "ordin.mm"
include "sylancl.mm"
include "ordeq.mm"
include "mpbird.mm"
include "ordelss.mm"
include "sylan.mm"
include "sselda.mm"
include "pm5.5.mm"
include "ralbidva.mm"
include "eldifn.mm"
include "ad2antlr.mm"
include "wfn.mm"
include "ad2antrr.mm"
include "ffn.mm"
include "simprl.mm"
include "eleqtrd.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "syl5ibcom.mm"
include "mtod.mm"
include "cima.mm"
include "crab.mm"
include "eldifi.mm"
include "simprr.mm"
include "cres.mm"
include "ordtypelem1.mm"
include "adantrr.mm"
include "sseqtrd.mm"
include "syl6ss.mm"
include "fveq1.mm"
include "ssel2.mm"
include "fvres.mm"
include "sylan9eq.mm"
include "anassrs.mm"
include "mpbid.mm"
include "simpli.mm"
include "funfn.mm"
include "mpbi.mm"
include "inss2.mm"
include "breq1.mm"
include "ralima.mm"
include "sylancr.mm"
include "breq2.mm"
include "ralbidv.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "fveq1d.mm"
include "sseldi.mm"
include "eqtrd.mm"
include "simpll.mm"
include "ordtypelem3.mm"
include "eqeltrd.mm"
include "notbid.mm"
include "simprbi.mm"
include "rspcv.mm"
include "sylc.mm"
include "wo.mm"
include "wor.mm"
include "wwe.mm"
include "weso.mm"
include "ffvelrnd.mm"
include "sotric.mm"
include "syl12anc.mm"
include "ioran.mm"
include "syl6bb.mm"
include "mpbir2and.mm"
include "expr.mm"
include "sylbid.mm"
include "ex.mm"
include "com23.mm"
include "a2i.mm"
include "a1i.mm"
include "syl5bi.mm"
include "tfis3.mm"
include "com3l.mm"
include "mpdd.mm"
include "sylan2br.mm"
include "impancom.mm"
include "orrd.mm"
include "orcomd.mm"

theorem ordtypelem7
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
  let cM: class M
  let cN: class N
  let cO: class O
  let vf: setvar f
  let vr: setvar r
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
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
  disjoint M h
  disjoint j t
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j z
  disjoint M j
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t z
  disjoint M t
  disjoint u w
  disjoint u x
  disjoint u z
  disjoint M u
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint M v
  disjoint w x
  disjoint w z
  disjoint M w
  disjoint x z
  disjoint M x
  disjoint M z
  disjoint N j
  disjoint N u
  disjoint N w
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
  disjoint a b
  disjoint N a
  disjoint b j
  disjoint b u
  disjoint b w
  disjoint N b
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
  assert |- ( ( ( ph /\ N e. A ) /\ M e. dom O ) -> ( ( O ` M ) R N \/ N e. ran O ) )

  proof
    wph
    cN
    cA
    wcel
    #
    wa
    #
    cM
    cO
    cdm
    #
    wcel
    #
    wa
    #
    cN
    cO
    crn
    #
    wcel
    #
    cM
    cO
    cfv
    #
    cN
    cR
    wbr
    #
    @4
    @6
    @8
    @1
    @6
    wn
    #
    @3
    @8
    wph
    @0
    @9
    @3
    @8
    wi
    #
    @0
    @9
    wa
    wph
    cN
    cA
    @5
    cdif
    wcel
    #
    @10
    cN
    cA
    @5
    eldif
    wph
    @11
    wa
    #
    @3
    cM
    con0
    wcel
    #
    @8
    @12
    @2
    con0
    cM
    @12
    @2
    cT
    cF
    cdm
    #
    cin
    #
    con0
    @12
    @15
    cA
    cO
    wf
    #
    @2
    @15
    wceq
    #
    wph
    @16
    @11
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
    adantr
    @15
    cA
    cO
    fdm
    #
    syl
    #
    @12
    @15
    cT
    con0
    cT
    @14
    inss1
    #
    @12
    cT
    word
    #
    cT
    con0
    wss
    wph
    @22
    @11
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
    adantr
    #
    cT
    ordsson
    syl
    syl5ss
    eqsstrd
    sseld
    @13
    @12
    @3
    @8
    @12
    va
    cv
    #
    @2
    wcel
    #
    @24
    cO
    cfv
    #
    cN
    cR
    wbr
    #
    wi
    #
    wi
    #
    @12
    vb
    cv
    #
    @2
    wcel
    #
    @30
    cO
    cfv
    #
    cN
    cR
    wbr
    #
    wi
    #
    wi
    #
    @12
    @10
    wi
    va
    vb
    cM
    @24
    @30
    wceq
    #
    @28
    @34
    @12
    @36
    @25
    @31
    @27
    @33
    @24
    @30
    @2
    eleq1
    @36
    @26
    @32
    cN
    cR
    @24
    @30
    cO
    fveq2
    breq1d
    imbi12d
    imbi2d
    @24
    cM
    wceq
    #
    @28
    @10
    @12
    @37
    @25
    @3
    @27
    @8
    @24
    cM
    @2
    eleq1
    @37
    @26
    @7
    cN
    cR
    @24
    cM
    cO
    fveq2
    breq1d
    imbi12d
    imbi2d
    @35
    vb
    @24
    wral
    @12
    @34
    vb
    @24
    wral
    #
    wi
    #
    @24
    con0
    wcel
    #
    @29
    @12
    @34
    vb
    @24
    r19.21v
    @39
    @29
    wi
    @40
    @12
    @38
    @28
    @12
    @25
    @38
    @27
    @12
    @25
    @38
    @27
    wi
    @12
    @25
    wa
    #
    @38
    @33
    vb
    @24
    wral
    #
    @27
    @41
    @34
    @33
    vb
    @24
    @41
    @30
    @24
    wcel
    #
    wa
    @31
    @34
    @33
    wb
    @41
    @24
    @2
    @30
    @12
    @2
    word
    #
    @25
    @24
    @2
    wss
    #
    @12
    @44
    @15
    word
    #
    @12
    @22
    @14
    word
    #
    @46
    @23
    @14
    wlim
    #
    @47
    cF
    wfun
    #
    @48
    cF
    cG
    ordtypelem.1
    tfr1a
    #
    simpri
    @14
    limord
    ax-mp
    cT
    @14
    ordin
    sylancl
    @12
    @17
    @44
    @46
    wb
    @20
    @2
    @15
    ordeq
    syl
    mpbird
    @2
    @24
    ordelss
    sylan
    #
    sselda
    @31
    @33
    pm5.5
    syl
    ralbidva
    @12
    @25
    @42
    @27
    @12
    @25
    @42
    wa
    #
    wa
    #
    @27
    @26
    cN
    wceq
    #
    wn
    #
    cN
    @26
    cR
    wbr
    #
    wn
    #
    @53
    @54
    @6
    @11
    @9
    wph
    @52
    cN
    cA
    @5
    eldifn
    ad2antlr
    @53
    @26
    @5
    wcel
    #
    @54
    @6
    @53
    cO
    @15
    wfn
    #
    @24
    @15
    wcel
    #
    @58
    @53
    @16
    @59
    wph
    @16
    @11
    @52
    @18
    ad2antrr
    #
    @15
    cA
    cO
    ffn
    syl
    @53
    @24
    @2
    @15
    @12
    @25
    @42
    simprl
    @53
    @16
    @17
    @61
    @19
    syl
    #
    eleqtrd
    #
    @15
    @24
    cO
    fnfvelrn
    syl2anc
    @26
    cN
    @5
    eleq1
    syl5ibcom
    mtod
    @53
    cN
    vj
    cv
    #
    vw
    cv
    #
    cR
    wbr
    #
    vj
    cF
    @24
    cima
    #
    wral
    #
    vw
    cA
    crab
    #
    wcel
    #
    vu
    cv
    #
    @26
    cR
    wbr
    #
    wn
    #
    vu
    @69
    wral
    #
    @57
    @53
    @0
    @64
    cN
    cR
    wbr
    #
    vj
    @67
    wral
    #
    @70
    @11
    @0
    wph
    @52
    cN
    cA
    @5
    eldifi
    ad2antlr
    #
    @53
    @76
    @30
    cF
    cfv
    #
    cN
    cR
    wbr
    #
    vb
    @24
    wral
    #
    @53
    @42
    @80
    @12
    @25
    @42
    simprr
    @53
    cO
    cF
    cT
    cres
    #
    wceq
    #
    @24
    cT
    wss
    #
    @42
    @80
    wb
    wph
    @82
    @11
    @52
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
    ad2antrr
    #
    @53
    @24
    @15
    cT
    @53
    @24
    @2
    @15
    @12
    @25
    @45
    @42
    @51
    adantrr
    @62
    sseqtrd
    #
    @21
    syl6ss
    @82
    @83
    wa
    #
    @33
    @79
    vb
    @24
    @86
    @43
    wa
    @32
    @78
    cN
    cR
    @82
    @83
    @43
    @32
    @78
    wceq
    @82
    @83
    @43
    wa
    #
    @32
    @30
    @81
    cfv
    #
    @78
    @30
    cO
    @81
    fveq1
    @87
    @30
    cT
    wcel
    @88
    @78
    wceq
    @24
    cT
    @30
    ssel2
    @30
    cT
    cF
    fvres
    syl
    sylan9eq
    anassrs
    breq1d
    ralbidva
    syl2anc
    mpbid
    @53
    cF
    @14
    wfn
    #
    @24
    @14
    wss
    @76
    @80
    wb
    @49
    @89
    @49
    @48
    @50
    simpli
    cF
    funfn
    mpbi
    @53
    @24
    @15
    @14
    @85
    cT
    @14
    inss2
    syl6ss
    @75
    @79
    vj
    vb
    @14
    @24
    cF
    @64
    @78
    cN
    cR
    breq1
    ralima
    sylancr
    mpbird
    @68
    @76
    vw
    cN
    cA
    @65
    cN
    wceq
    @66
    @75
    vj
    @67
    @65
    cN
    @64
    cR
    breq2
    ralbidv
    elrab
    sylanbrc
    @53
    @26
    @71
    vv
    cv
    #
    cR
    wbr
    #
    wn
    #
    vu
    @69
    wral
    #
    vv
    @69
    crab
    #
    wcel
    #
    @74
    @53
    @26
    @24
    cF
    cfv
    #
    @94
    @53
    @26
    @24
    @81
    cfv
    #
    @96
    @53
    @24
    cO
    @81
    @84
    fveq1d
    @53
    @24
    cT
    wcel
    @97
    @96
    wceq
    @53
    @15
    cT
    @24
    @21
    @63
    sseldi
    @24
    cT
    cF
    fvres
    syl
    eqtrd
    @53
    wph
    @60
    @96
    @94
    wcel
    wph
    @11
    @52
    simpll
    @63
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
    @24
    cO
    ordtypelem.1
    ordtypelem.2
    ordtypelem.3
    ordtypelem.5
    ordtypelem.6
    ordtypelem.7
    ordtypelem.8
    ordtypelem3
    syl2anc
    eqeltrd
    @95
    @26
    @69
    wcel
    @74
    @93
    @74
    vv
    @26
    @69
    @90
    @26
    wceq
    #
    @92
    @73
    vu
    @69
    @98
    @91
    @72
    @90
    @26
    @71
    cR
    breq2
    notbid
    ralbidv
    elrab
    simprbi
    syl
    @73
    @57
    vu
    cN
    @69
    @71
    cN
    wceq
    @72
    @56
    @71
    cN
    @26
    cR
    breq1
    notbid
    rspcv
    sylc
    @53
    @27
    @54
    @56
    wo
    wn
    #
    @55
    @57
    wa
    @53
    cA
    cR
    wor
    #
    @26
    cA
    wcel
    @0
    @27
    @99
    wb
    wph
    @100
    @11
    @52
    wph
    cA
    cR
    wwe
    @100
    ordtypelem.7
    cA
    cR
    weso
    syl
    ad2antrr
    @53
    @15
    cA
    @24
    cO
    @61
    @63
    ffvelrnd
    @77
    cA
    @26
    cN
    cR
    sotric
    syl12anc
    @54
    @56
    ioran
    syl6bb
    mpbir2and
    expr
    sylbid
    ex
    com23
    a2i
    a1i
    syl5bi
    tfis3
    com3l
    mpdd
    sylan2br
    anassrs
    impancom
    orrd
    orcomd
end
