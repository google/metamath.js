include "ctsu.mm"
include "co.mm"
include "ccom.mm"
include "cv.mm"
include "wcel.mm"
include "wss.mm"
include "cres.mm"
include "cgsu.mm"
include "wi.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wral.mm"
include "wrex.mm"
include "ctopn.mm"
include "cfv.mm"
include "wa.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "wb.mm"
include "wf.mm"
include "wf1o.mm"
include "f1opwfi.mm"
include "syl.mm"
include "f1of.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "wceq.mm"
include "sseq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rexrnmpt.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"
include "rexeqdv.mm"
include "imaeq2.mm"
include "cbvmptv.mm"
include "sseq2.mm"
include "reseq2.mm"
include "oveq2d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "ralrnmpt.mm"
include "raleqdv.mm"
include "bitr3d.mm"
include "adantr.mm"
include "wf1.mm"
include "f1of1.mm"
include "ad2antrr.mm"
include "elfpw.mm"
include "simplbi.mm"
include "ad2antlr.mm"
include "adantl.mm"
include "f1imass.mm"
include "syl12anc.mm"
include "c0g.mm"
include "ccmn.mm"
include "simprbi.mm"
include "f1ores.mm"
include "syl2anc.mm"
include "fofi.mm"
include "imassrn.mm"
include "syl5sseq.mm"
include "fssresd.mm"
include "cvv.mm"
include "fvexd.mm"
include "fdmfifsupp.mm"
include "gsumf1o.mm"
include "df-ima.mm"
include "eqimss2i.mm"
include "cores.mm"
include "ax-mp.mm"
include "resco.mm"
include "eqtr4i.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "3bitr3d.mm"
include "imbi2d.mm"
include "anbi2d.mm"
include "eltsms.mm"
include "f1dmex.mm"
include "fco.mm"
include "3bitr4d.mm"
include "eqrdv.mm"

theorem tsmsf1o
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vy: setvar y
  let vz: setvar z
  let vx: setvar x
  assume tsmsf1o.b: |- B = ( Base ` G )
  assume tsmsf1o.1: |- ( ph -> G e. CMnd )
  assume tsmsf1o.2: |- ( ph -> G e. TopSp )
  assume tsmsf1o.a: |- ( ph -> A e. V )
  assume tsmsf1o.f: |- ( ph -> F : A --> B )
  assume tsmsf1o.s: |- ( ph -> H : C -1-1-onto-> A )


  assert |- ( ph -> ( G tsums F ) = ( G tsums ( F o. H ) ) )

  proof
    wph
    vx
    cG
    cF
    ctsu
    co
    #
    cG
    cF
    cH
    ccom
    #
    ctsu
    co
    #
    wph
    vx
    cv
    #
    cB
    wcel
    #
    @3
    vu
    cv
    #
    wcel
    #
    vy
    cv
    #
    vz
    cv
    #
    wss
    #
    cG
    cF
    @8
    cres
    #
    cgsu
    co
    #
    @5
    wcel
    #
    wi
    #
    vz
    cA
    cpw
    cfn
    cin
    #
    wral
    #
    vy
    @14
    wrex
    #
    wi
    #
    vu
    cG
    ctopn
    cfv
    #
    wral
    #
    wa
    @4
    @6
    va
    cv
    #
    vb
    cv
    #
    wss
    #
    cG
    @1
    @21
    cres
    #
    cgsu
    co
    #
    @5
    wcel
    #
    wi
    #
    vb
    cC
    cpw
    cfn
    cin
    #
    wral
    #
    va
    @27
    wrex
    #
    wi
    #
    vu
    @18
    wral
    #
    wa
    @3
    @0
    wcel
    @3
    @2
    wcel
    wph
    @19
    @31
    @4
    wph
    @17
    @30
    vu
    @18
    wph
    @16
    @29
    @6
    wph
    @15
    vy
    va
    @27
    cH
    @20
    cima
    #
    cmpt
    #
    crn
    #
    wrex
    #
    @32
    @8
    wss
    #
    @12
    wi
    #
    vz
    @14
    wral
    #
    va
    @27
    wrex
    #
    @16
    @29
    wph
    @32
    @14
    wcel
    va
    @27
    wral
    #
    @35
    @39
    wb
    wph
    @27
    @14
    @33
    wf
    #
    @40
    wph
    @27
    @14
    @33
    wf1o
    #
    @41
    wph
    cC
    cA
    cH
    wf1o
    #
    @42
    tsmsf1o.s
    cC
    cA
    cH
    va
    f1opwfi
    syl
    #
    @27
    @14
    @33
    f1of
    syl
    #
    va
    @27
    @14
    @32
    @33
    @33
    eqid
    #
    fmpt
    sylibr
    @15
    @38
    va
    vy
    @27
    @32
    @33
    @14
    @46
    @7
    @32
    wceq
    #
    @13
    @37
    vz
    @14
    @47
    @9
    @36
    @12
    @7
    @32
    @8
    sseq1
    imbi1d
    ralbidv
    rexrnmpt
    syl
    wph
    @15
    vy
    @34
    @14
    wph
    @42
    @27
    @14
    @33
    wfo
    @34
    @14
    wceq
    @44
    @27
    @14
    @33
    f1ofo
    @27
    @14
    @33
    forn
    3syl
    #
    rexeqdv
    wph
    @38
    @28
    va
    @27
    wph
    @20
    @27
    wcel
    #
    wa
    #
    @32
    cH
    @21
    cima
    #
    wss
    #
    cG
    cF
    @51
    cres
    #
    cgsu
    co
    #
    @5
    wcel
    #
    wi
    #
    vb
    @27
    wral
    #
    @38
    @28
    wph
    @57
    @38
    wb
    @49
    wph
    @37
    vz
    @34
    wral
    #
    @57
    @38
    wph
    @51
    @14
    wcel
    vb
    @27
    wral
    #
    @58
    @57
    wb
    wph
    @41
    @59
    @45
    vb
    @27
    @14
    @51
    @33
    va
    vb
    @27
    @32
    @51
    @20
    @21
    cH
    imaeq2
    cbvmptv
    #
    fmpt
    sylibr
    @37
    @56
    vb
    vz
    @27
    @51
    @33
    @14
    @60
    @8
    @51
    wceq
    #
    @36
    @52
    @12
    @55
    @8
    @51
    @32
    sseq2
    @61
    @11
    @54
    @5
    @61
    @10
    @53
    cG
    cgsu
    @8
    @51
    cF
    reseq2
    oveq2d
    eleq1d
    imbi12d
    ralrnmpt
    syl
    wph
    @37
    vz
    @34
    @14
    @48
    raleqdv
    bitr3d
    adantr
    @50
    @56
    @26
    vb
    @27
    @50
    @21
    @27
    wcel
    #
    wa
    #
    @52
    @22
    @55
    @25
    @63
    cC
    cA
    cH
    wf1
    #
    @20
    cC
    wss
    #
    @21
    cC
    wss
    #
    @52
    @22
    wb
    wph
    @64
    @49
    @62
    wph
    @43
    @64
    tsmsf1o.s
    cC
    cA
    cH
    f1of1
    syl
    #
    ad2antrr
    #
    @49
    @65
    wph
    @62
    @49
    @65
    @20
    cfn
    wcel
    @20
    cC
    elfpw
    simplbi
    ad2antlr
    @62
    @66
    @50
    @62
    @66
    @21
    cfn
    wcel
    #
    @21
    cC
    elfpw
    #
    simplbi
    adantl
    #
    cC
    cA
    @20
    @21
    cH
    f1imass
    syl12anc
    @63
    @54
    @24
    @5
    @63
    @54
    cG
    @53
    cH
    @21
    cres
    #
    ccom
    #
    cgsu
    co
    @24
    @63
    @51
    cB
    @21
    @53
    cG
    @72
    cfn
    cG
    c0g
    cfv
    #
    tsmsf1o.b
    @74
    eqid
    wph
    cG
    ccmn
    wcel
    @49
    @62
    tsmsf1o.1
    ad2antrr
    @63
    @69
    @21
    @51
    @72
    wfo
    #
    @51
    cfn
    wcel
    @62
    @69
    @50
    @62
    @66
    @69
    @70
    simprbi
    adantl
    @63
    @21
    @51
    @72
    wf1o
    #
    @75
    @63
    @64
    @66
    @76
    @68
    @71
    cC
    cA
    @21
    cH
    f1ores
    syl2anc
    #
    @21
    @51
    @72
    f1ofo
    syl
    @21
    @51
    @72
    fofi
    syl2anc
    #
    @63
    cA
    cB
    @51
    cF
    wph
    cA
    cB
    cF
    wf
    #
    @49
    @62
    tsmsf1o.f
    ad2antrr
    @63
    cH
    crn
    #
    @51
    cA
    cH
    @21
    imassrn
    @63
    @43
    cC
    cA
    cH
    wfo
    @80
    cA
    wceq
    wph
    @43
    @49
    @62
    tsmsf1o.s
    ad2antrr
    cC
    cA
    cH
    f1ofo
    cC
    cA
    cH
    forn
    3syl
    syl5sseq
    fssresd
    #
    @63
    @51
    cB
    @53
    cvv
    @74
    @81
    @78
    @63
    cG
    c0g
    fvexd
    fdmfifsupp
    @77
    gsumf1o
    @73
    @23
    cG
    cgsu
    @73
    cF
    @72
    ccom
    #
    @23
    @72
    crn
    #
    @51
    wss
    @73
    @82
    wceq
    @51
    @83
    cH
    @21
    df-ima
    eqimss2i
    cF
    @72
    @51
    cores
    ax-mp
    cF
    cH
    @21
    resco
    eqtr4i
    oveq2i
    syl6eq
    eleq1d
    imbi12d
    ralbidva
    bitr3d
    rexbidva
    3bitr3d
    imbi2d
    ralbidv
    anbi2d
    wph
    vz
    vy
    vu
    cA
    cB
    @3
    @14
    cF
    cG
    @18
    cV
    tsmsf1o.b
    @18
    eqid
    #
    @14
    eqid
    tsmsf1o.1
    tsmsf1o.2
    tsmsf1o.a
    tsmsf1o.f
    eltsms
    wph
    vb
    va
    vu
    cC
    cB
    @3
    @27
    @1
    cG
    @18
    cvv
    tsmsf1o.b
    @84
    @27
    eqid
    tsmsf1o.1
    tsmsf1o.2
    wph
    @64
    cA
    cV
    wcel
    cC
    cvv
    wcel
    @67
    tsmsf1o.a
    cC
    cA
    cV
    cH
    f1dmex
    syl2anc
    wph
    @79
    cC
    cA
    cH
    wf
    #
    cC
    cB
    @1
    wf
    tsmsf1o.f
    wph
    @43
    @85
    tsmsf1o.s
    cC
    cA
    cH
    f1of
    syl
    cC
    cA
    cB
    cF
    cH
    fco
    syl2anc
    eltsms
    3bitr4d
    eqrdv
end
