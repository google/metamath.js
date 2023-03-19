include "cioo.mm"
include "co.mm"
include "cv.mm"
include "cr.mm"
include "cicc.mm"
include "cres.mm"
include "cdv.mm"
include "cfv.mm"
include "citg.mm"
include "cmin.mm"
include "wss.mm"
include "ioossre.mm"
include "eqsstri.mm"
include "a1i.mm"
include "sseldd.mm"
include "cc.mm"
include "ccncf.mm"
include "crn.mm"
include "ctg.mm"
include "cnt.mm"
include "wf.mm"
include "wceq.mm"
include "ax-resscn.mm"
include "wcel.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "tgioo2.mm"
include "dvres.mm"
include "syl22anc.mm"
include "iccntr.mm"
include "reseq2d.mm"
include "eqtrd.mm"
include "ioossicc.mm"
include "fct2relem.mm"
include "sstrd.mm"
include "rescncf.mm"
include "sylc.mm"
include "eqeltrd.mm"
include "cibl.mm"
include "cmbf.mm"
include "cdm.mm"
include "cvol.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "ioombl.mm"
include "cnmbf.mm"
include "cin.mm"
include "dmres.mm"
include "fveq2i.mm"
include "cncff.mm"
include "syl.mm"
include "fdm.mm"
include "ineq2d.mm"
include "df-ss.mm"
include "sylib.mm"
include "fveq2d.mm"
include "volioo.mm"
include "syl3anc.mm"
include "resubcld.mm"
include "syl5eqel.mm"
include "wi.mm"
include "mpd.mm"
include "cniccbdd.mm"
include "wa.mm"
include "syl5eq.mm"
include "eqsstrd.mm"
include "ssralv.mm"
include "adantr.mm"
include "sselda.mm"
include "fvres.mm"
include "simpr.mm"
include "ad2antrr.mm"
include "eleqtrd.mm"
include "eqtr4d.mm"
include "breq1d.mm"
include "biimpd.mm"
include "ralimdva.mm"
include "syld.mm"
include "reximdva.mm"
include "bddibl.mm"
include "dvcn.mm"
include "syl31anc.mm"
include "ftc2.mm"
include "fveq1d.mm"
include "sylan9eq.mm"
include "ralrimiva.mm"
include "itgeq2.mm"
include "cxr.mm"
include "rexrd.mm"
include "ubicc2.mm"
include "fvresd.mm"
include "lbicc2.mm"
include "oveq12d.mm"
include "3eqtr3d.mm"

theorem ftc2re
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  assume ftc2re.e: |- E = ( C (,) D )
  assume ftc2re.a: |- ( ph -> A e. E )
  assume ftc2re.b: |- ( ph -> B e. E )
  assume ftc2re.le: |- ( ph -> A <_ B )
  assume ftc2re.f: |- ( ph -> F : E --> CC )
  assume ftc2re.1: |- ( ph -> ( RR _D F ) e. ( E -cn-> CC ) )

  disjoint A t
  disjoint B t
  disjoint F t
  disjoint ph t
  disjoint t x
  disjoint t y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint E x
  disjoint F x
  disjoint F y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> S. ( A (,) B ) ( ( RR _D F ) ` t ) _d t = ( ( F ` B ) - ( F ` A ) ) )

  proof
    wph
    vt
    cA
    cB
    cioo
    co
    #
    vt
    cv
    #
    cr
    cF
    cA
    cB
    cicc
    co
    #
    cres
    #
    cdv
    co
    #
    cfv
    #
    citg
    #
    cB
    @3
    cfv
    #
    cA
    @3
    cfv
    #
    cmin
    co
    vt
    @0
    @1
    cr
    cF
    cdv
    co
    #
    cfv
    #
    citg
    #
    cB
    cF
    cfv
    #
    cA
    cF
    cfv
    #
    cmin
    co
    wph
    vt
    cA
    cB
    @3
    wph
    cE
    cr
    cA
    cE
    cr
    wss
    #
    wph
    cE
    cC
    cD
    cioo
    co
    cr
    ftc2re.e
    cC
    cD
    ioossre
    eqsstri
    a1i
    #
    ftc2re.a
    sseldd
    #
    wph
    cE
    cr
    cB
    @15
    ftc2re.b
    sseldd
    #
    ftc2re.le
    wph
    @4
    @9
    @0
    cres
    #
    @0
    cc
    ccncf
    co
    #
    wph
    @4
    @9
    @2
    cioo
    crn
    ctg
    cfv
    #
    cnt
    cfv
    cfv
    #
    cres
    #
    @18
    wph
    cr
    cc
    wss
    #
    cE
    cc
    cF
    wf
    #
    @14
    @2
    cr
    wss
    #
    @4
    @22
    wceq
    @23
    wph
    ax-resscn
    a1i
    #
    ftc2re.f
    @15
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @25
    @16
    @17
    cA
    cB
    iccssre
    syl2anc
    cE
    @2
    cr
    @20
    cF
    ccnfld
    ctopn
    cfv
    #
    @29
    eqid
    #
    @29
    @30
    tgioo2
    dvres
    syl22anc
    wph
    @21
    @0
    @9
    wph
    @27
    @28
    @21
    @0
    wceq
    @16
    @17
    cA
    cB
    iccntr
    syl2anc
    reseq2d
    eqtrd
    #
    wph
    @0
    cE
    wss
    #
    @9
    cE
    cc
    ccncf
    co
    #
    wcel
    #
    @18
    @19
    wcel
    #
    wph
    @0
    @2
    cE
    @0
    @2
    wss
    wph
    cA
    cB
    ioossicc
    a1i
    #
    wph
    cA
    cB
    cC
    cD
    cE
    ftc2re.e
    ftc2re.a
    ftc2re.b
    fct2relem
    #
    sstrd
    #
    ftc2re.1
    cE
    cc
    @0
    @9
    rescncf
    sylc
    #
    eqeltrd
    wph
    @4
    @18
    cibl
    @31
    wph
    @18
    cmbf
    wcel
    #
    @18
    cdm
    #
    cvol
    cfv
    #
    cr
    wcel
    vy
    cv
    #
    @18
    cfv
    #
    cabs
    cfv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vy
    @41
    wral
    #
    vx
    cr
    wrex
    #
    @18
    cibl
    wcel
    wph
    @0
    cvol
    cdm
    wcel
    #
    @35
    @40
    @50
    wph
    cA
    cB
    ioombl
    a1i
    @39
    @0
    @18
    cnmbf
    syl2anc
    wph
    @42
    @0
    @9
    cdm
    #
    cin
    #
    cvol
    cfv
    #
    cr
    @41
    @52
    cvol
    @9
    @0
    dmres
    #
    fveq2i
    wph
    @53
    @0
    cvol
    cfv
    #
    cr
    wph
    @52
    @0
    cvol
    wph
    @52
    @0
    cE
    cin
    #
    @0
    wph
    @51
    cE
    @0
    wph
    cE
    cc
    @9
    wf
    #
    @51
    cE
    wceq
    #
    wph
    @34
    @57
    ftc2re.1
    cE
    cc
    @9
    cncff
    syl
    cE
    cc
    @9
    fdm
    syl
    #
    ineq2d
    wph
    @32
    @56
    @0
    wceq
    @38
    @0
    cE
    df-ss
    sylib
    eqtrd
    #
    fveq2d
    wph
    @55
    cB
    cA
    cmin
    co
    #
    cr
    wph
    @27
    @28
    cA
    cB
    cle
    wbr
    #
    @55
    @61
    wceq
    @16
    @17
    ftc2re.le
    cA
    cB
    volioo
    syl3anc
    wph
    cB
    cA
    @17
    @16
    resubcld
    eqeltrd
    eqeltrd
    syl5eqel
    wph
    @43
    @9
    @2
    cres
    #
    cfv
    #
    cabs
    cfv
    #
    @46
    cle
    wbr
    #
    vy
    @2
    wral
    #
    vx
    cr
    wrex
    #
    @49
    wph
    @27
    @28
    @63
    @2
    cc
    ccncf
    co
    #
    wcel
    #
    @68
    @16
    @17
    wph
    @34
    @70
    ftc2re.1
    wph
    @2
    cE
    wss
    #
    @34
    @70
    wi
    @37
    cE
    cc
    @2
    @9
    rescncf
    syl
    mpd
    vx
    vy
    cA
    cB
    @63
    cniccbdd
    syl3anc
    wph
    @67
    @48
    vx
    cr
    wph
    @46
    cr
    wcel
    #
    wa
    #
    @67
    @66
    vy
    @41
    wral
    #
    @48
    wph
    @67
    @74
    wi
    #
    @72
    wph
    @41
    @2
    wss
    #
    @75
    wph
    @41
    @0
    @2
    wph
    @41
    @52
    @0
    @54
    @60
    syl5eq
    #
    @36
    eqsstrd
    #
    @66
    vy
    @41
    @2
    ssralv
    syl
    adantr
    @73
    @66
    @47
    vy
    @41
    @73
    @43
    @41
    wcel
    #
    wa
    #
    @66
    @47
    @80
    @65
    @45
    @46
    cle
    @80
    @64
    @44
    cabs
    @80
    @64
    @43
    @9
    cfv
    #
    @44
    @80
    @43
    @2
    wcel
    @64
    @81
    wceq
    @73
    @41
    @2
    @43
    wph
    @76
    @72
    @78
    adantr
    sselda
    @43
    @2
    @9
    fvres
    syl
    @80
    @43
    @0
    wcel
    @44
    @81
    wceq
    @80
    @43
    @41
    @0
    @73
    @79
    simpr
    wph
    @41
    @0
    wceq
    @72
    @79
    @77
    ad2antrr
    eleqtrd
    @43
    @0
    @9
    fvres
    syl
    eqtr4d
    fveq2d
    breq1d
    biimpd
    ralimdva
    syld
    reximdva
    mpd
    vx
    vy
    @18
    bddibl
    syl3anc
    eqeltrd
    wph
    cF
    @33
    wcel
    #
    @3
    @69
    wcel
    #
    wph
    @23
    @24
    @14
    @58
    @82
    @26
    ftc2re.f
    @15
    @59
    cE
    cr
    cF
    dvcn
    syl31anc
    wph
    @71
    @82
    @83
    wi
    @37
    cE
    cc
    @2
    cF
    rescncf
    syl
    mpd
    ftc2
    wph
    @5
    @10
    wceq
    #
    vt
    @0
    wral
    @6
    @11
    wceq
    wph
    @84
    vt
    @0
    wph
    @1
    @0
    wcel
    @5
    @1
    @18
    cfv
    @10
    wph
    @1
    @4
    @18
    @31
    fveq1d
    @1
    @0
    @9
    fvres
    sylan9eq
    ralrimiva
    vt
    @0
    @5
    @10
    itgeq2
    syl
    wph
    @7
    @12
    @8
    @13
    cmin
    wph
    cB
    @2
    cF
    wph
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @62
    cB
    @2
    wcel
    wph
    cA
    @16
    rexrd
    #
    wph
    cB
    @17
    rexrd
    #
    ftc2re.le
    cA
    cB
    ubicc2
    syl3anc
    fvresd
    wph
    cA
    @2
    cF
    wph
    @85
    @86
    @62
    cA
    @2
    wcel
    @87
    @88
    ftc2re.le
    cA
    cB
    lbicc2
    syl3anc
    fvresd
    oveq12d
    3eqtr3d
end
