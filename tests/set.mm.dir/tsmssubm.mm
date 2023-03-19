include "ctsu.mm"
include "co.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wss.mm"
include "cres.mm"
include "cgsu.mm"
include "wi.mm"
include "cpw.mm"
include "cfn.mm"
include "wral.mm"
include "wrex.mm"
include "ctopn.mm"
include "cfv.mm"
include "wa.mm"
include "cbs.mm"
include "csubmnd.mm"
include "wceq.mm"
include "submbas.mm"
include "syl.mm"
include "eleq2d.mm"
include "anbi1d.mm"
include "elin.mm"
include "ancom.mm"
include "bitri.mm"
include "wb.mm"
include "eqid.mm"
include "submss.mm"
include "sselda.mm"
include "fssd.mm"
include "eltsms.mm"
include "baibd.mm"
include "syldan.mm"
include "cvv.mm"
include "vex.mm"
include "inex1.mm"
include "a1i.mm"
include "crest.mm"
include "resstopn.mm"
include "eleq2i.mm"
include "fvex.mm"
include "elrest.mm"
include "sylancr.mm"
include "adantr.mm"
include "syl5bbr.mm"
include "eleq2.mm"
include "rbaib.mm"
include "adantl.mm"
include "sylan9bbr.mm"
include "c0g.mm"
include "ccmn.mm"
include "cmnd.mm"
include "submmnd.mm"
include "subcmn.mm"
include "syl2anc.mm"
include "ad2antrr.mm"
include "elfpw.mm"
include "simprbi.mm"
include "wf.mm"
include "simplbi.mm"
include "fssresd.mm"
include "feq3d.mm"
include "mpbid.mm"
include "fdmfifsupp.mm"
include "gsumcl.mm"
include "eleqtrrd.mm"
include "gsumsubm.mm"
include "eleq1d.mm"
include "bitr4d.mm"
include "an32s.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "ralxfr2d.mm"
include "pm5.32da.mm"
include "syl5bb.mm"
include "cress.mm"
include "ctps.mm"
include "resstps.mm"
include "syl5eqel.mm"
include "3bitr4rd.mm"
include "eqrdv.mm"

theorem tsmssubm
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume tsmssubm.a: |- ( ph -> A e. V )
  assume tsmssubm.1: |- ( ph -> G e. CMnd )
  assume tsmssubm.2: |- ( ph -> G e. TopSp )
  assume tsmssubm.s: |- ( ph -> S e. ( SubMnd ` G ) )
  assume tsmssubm.f: |- ( ph -> F : A --> S )
  assume tsmssubm.h: |- H = ( G |`s S )


  assert |- ( ph -> ( H tsums F ) = ( ( G tsums F ) i^i S ) )

  proof
    wph
    vx
    cH
    cF
    ctsu
    co
    #
    cG
    cF
    ctsu
    co
    #
    cS
    cin
    #
    wph
    vx
    cv
    #
    cS
    wcel
    #
    @3
    vv
    cv
    #
    wcel
    #
    vz
    cv
    vy
    cv
    #
    wss
    #
    cH
    cF
    @7
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
    vy
    cA
    cpw
    cfn
    cin
    #
    wral
    #
    vz
    @13
    wrex
    #
    wi
    #
    vv
    cH
    ctopn
    cfv
    #
    wral
    #
    wa
    #
    @3
    cH
    cbs
    cfv
    #
    wcel
    #
    @18
    wa
    @3
    @2
    wcel
    #
    @3
    @0
    wcel
    wph
    @4
    @21
    @18
    wph
    cS
    @20
    @3
    wph
    cS
    cG
    csubmnd
    cfv
    #
    wcel
    #
    cS
    @20
    wceq
    #
    tsmssubm.s
    cS
    cH
    cG
    tsmssubm.h
    submbas
    syl
    #
    eleq2d
    anbi1d
    @22
    @4
    @3
    @1
    wcel
    #
    wa
    #
    wph
    @19
    @22
    @27
    @4
    wa
    @28
    @3
    @1
    cS
    elin
    @27
    @4
    ancom
    bitri
    wph
    @4
    @27
    @18
    wph
    @4
    wa
    #
    @27
    @3
    vu
    cv
    #
    wcel
    #
    @8
    cG
    @9
    cgsu
    co
    #
    @30
    wcel
    #
    wi
    #
    vy
    @13
    wral
    #
    vz
    @13
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
    @18
    wph
    @4
    @3
    cG
    cbs
    cfv
    #
    wcel
    #
    @27
    @39
    wb
    wph
    cS
    @40
    @3
    wph
    @24
    cS
    @40
    wss
    tsmssubm.s
    @40
    cS
    cG
    @40
    eqid
    #
    submss
    syl
    #
    sselda
    wph
    @27
    @41
    @39
    wph
    vy
    vz
    vu
    cA
    @40
    @3
    @13
    cF
    cG
    @38
    cV
    @42
    @38
    eqid
    #
    @13
    eqid
    #
    tsmssubm.1
    tsmssubm.2
    tsmssubm.a
    wph
    cA
    cS
    @40
    cF
    tsmssubm.f
    @43
    fssd
    eltsms
    baibd
    syldan
    @29
    @16
    @37
    vv
    vu
    @30
    cS
    cin
    #
    @17
    @38
    cvv
    @46
    cvv
    wcel
    @29
    @30
    @38
    wcel
    wa
    @30
    cS
    vu
    vex
    inex1
    a1i
    @5
    @17
    wcel
    @5
    @38
    cS
    crest
    co
    #
    wcel
    #
    @29
    @5
    @46
    wceq
    #
    vu
    @38
    wrex
    #
    @47
    @17
    @5
    cS
    cH
    @38
    cG
    tsmssubm.h
    @44
    resstopn
    eleq2i
    wph
    @48
    @50
    wb
    #
    @4
    wph
    @38
    cvv
    wcel
    @24
    @51
    cG
    ctopn
    fvex
    tsmssubm.s
    vu
    @5
    cS
    @38
    cvv
    @23
    elrest
    sylancr
    adantr
    syl5bbr
    @29
    @49
    wa
    #
    @6
    @31
    @15
    @36
    @49
    @6
    @3
    @46
    wcel
    #
    @29
    @31
    @5
    @46
    @3
    eleq2
    @4
    @53
    @31
    wb
    wph
    @53
    @31
    @4
    @3
    @30
    cS
    elin
    rbaib
    adantl
    sylan9bbr
    @52
    @14
    @35
    vz
    @13
    @52
    @12
    @34
    vy
    @13
    @52
    @7
    @13
    wcel
    #
    wa
    @11
    @33
    @8
    @29
    @54
    @49
    @11
    @33
    wb
    @49
    @11
    @10
    @46
    wcel
    #
    @29
    @54
    wa
    #
    @33
    @5
    @46
    @10
    eleq2
    @56
    @55
    @10
    @30
    wcel
    #
    @33
    @56
    @10
    cS
    wcel
    #
    @55
    @57
    wb
    @56
    @10
    @20
    cS
    @56
    @7
    @20
    @9
    cH
    cfn
    cH
    c0g
    cfv
    #
    @20
    eqid
    #
    @59
    eqid
    wph
    cH
    ccmn
    wcel
    #
    @4
    @54
    wph
    cG
    ccmn
    wcel
    cH
    cmnd
    wcel
    #
    @61
    tsmssubm.1
    wph
    @24
    @62
    tsmssubm.s
    cS
    cH
    cG
    tsmssubm.h
    submmnd
    syl
    cS
    cG
    cH
    tsmssubm.h
    subcmn
    syl2anc
    #
    ad2antrr
    @54
    @7
    cfn
    wcel
    #
    @29
    @54
    @7
    cA
    wss
    #
    @64
    @7
    cA
    elfpw
    #
    simprbi
    adantl
    #
    @56
    @7
    cS
    @9
    wf
    @7
    @20
    @9
    wf
    @56
    cA
    cS
    @7
    cF
    wph
    cA
    cS
    cF
    wf
    #
    @4
    @54
    tsmssubm.f
    ad2antrr
    @54
    @65
    @29
    @54
    @65
    @64
    @66
    simplbi
    adantl
    fssresd
    #
    @56
    cS
    @20
    @9
    @7
    wph
    @25
    @4
    @54
    @26
    ad2antrr
    #
    feq3d
    mpbid
    @56
    @7
    cS
    @9
    cvv
    @59
    @69
    @67
    @59
    cvv
    wcel
    @56
    cH
    c0g
    fvex
    a1i
    fdmfifsupp
    gsumcl
    @70
    eleqtrrd
    @55
    @57
    @58
    @10
    @30
    cS
    elin
    rbaib
    syl
    @56
    @32
    @10
    @30
    @56
    @7
    cS
    @9
    cG
    cH
    cfn
    @67
    wph
    @24
    @4
    @54
    tsmssubm.s
    ad2antrr
    @69
    tsmssubm.h
    gsumsubm
    eleq1d
    bitr4d
    sylan9bbr
    an32s
    imbi2d
    ralbidva
    rexbidv
    imbi12d
    ralxfr2d
    bitr4d
    pm5.32da
    syl5bb
    wph
    vy
    vz
    vv
    cA
    @20
    @3
    @13
    cF
    cH
    @17
    cV
    @60
    @17
    eqid
    @45
    @63
    wph
    cH
    cG
    cS
    cress
    co
    #
    ctps
    tsmssubm.h
    wph
    cG
    ctps
    wcel
    @24
    @71
    ctps
    wcel
    tsmssubm.2
    tsmssubm.s
    cS
    cG
    @23
    resstps
    syl2anc
    syl5eqel
    tsmssubm.a
    wph
    @68
    cA
    @20
    cF
    wf
    tsmssubm.f
    wph
    cS
    @20
    cF
    cA
    @26
    feq3d
    mpbid
    eltsms
    3bitr4rd
    eqrdv
end
