include "cmbfm.mm"
include "co.mm"
include "wcel.mm"
include "cuni.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "wa.mm"
include "csiga.mm"
include "crn.mm"
include "adantr.mm"
include "csigagen.mm"
include "cfv.mm"
include "cvv.mm"
include "sgsiga.mm"
include "eqeltrd.mm"
include "simpr.mm"
include "mbfmf.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "wss.mm"
include "sssigagen.mm"
include "syl.mm"
include "sseqtr4d.mm"
include "sseldd.mm"
include "mbfmcnvima.mm"
include "ralrimiva.mm"
include "jca.mm"
include "cmap.mm"
include "unielsiga.mm"
include "simprl.mm"
include "elmapg.mm"
include "biimpar.mm"
include "syl21anc.mm"
include "crab.mm"
include "wceq.mm"
include "cpw.mm"
include "cdif.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "w3a.mm"
include "simpl.mm"
include "ssrab2.mm"
include "pwuni.mm"
include "sstri.mm"
include "a1i.mm"
include "fimacnv.mm"
include "ad2antrl.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "elrabi.mm"
include "adantl.mm"
include "difelsiga.mm"
include "syl3anc.mm"
include "wfun.mm"
include "simplrl.mm"
include "ffun.mm"
include "difpreima.mm"
include "3syl.mm"
include "difeq1d.mm"
include "simprbi.mm"
include "ad3antrrr.mm"
include "sspwb.mm"
include "mpbi.mm"
include "sseli.mm"
include "ad2antlr.mm"
include "sigaclcu.mm"
include "ciun.mm"
include "simpllr.mm"
include "simpld.mm"
include "unipreima.mm"
include "elelpwi.mm"
include "syl2anc.mm"
include "nfcv.mm"
include "sigaclcuni.mm"
include "ex.mm"
include "3jca.mm"
include "wb.mm"
include "rabexg.mm"
include "issiga.mm"
include "syl12anc.mm"
include "unieqd.mm"
include "unisg.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "mpbid.mm"
include "simprr.mm"
include "ssrab.mm"
include "sigagenss.mm"
include "eqsstrd.mm"
include "eqssd.mm"
include "rabid2.mm"
include "sylib.mm"
include "ismbfm.mm"
include "mpbir2and.mm"
include "impbida.mm"

theorem imambfm
  let wph: wff ph
  let cS: class S
  let cT: class T
  let cF: class F
  let cK: class K
  let va: setvar a
  let vx: setvar x
  let vy: setvar y
  assume imambfm.1: |- ( ph -> K e. _V )
  assume imambfm.2: |- ( ph -> S e. U. ran sigAlgebra )
  assume imambfm.3: |- ( ph -> T = ( sigaGen ` K ) )

  disjoint F a
  disjoint K a
  disjoint S a
  disjoint T a
  disjoint a ph
  disjoint a x
  disjoint a y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint K x
  disjoint K y
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint T y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( F e. ( S MblFnM T ) <-> ( F : U. S --> U. T /\ A. a e. K ( `' F " a ) e. S ) ) )

  proof
    wph
    cF
    cS
    cT
    cmbfm
    co
    wcel
    #
    cS
    cuni
    #
    cT
    cuni
    #
    cF
    wf
    #
    cF
    ccnv
    #
    va
    cv
    #
    cima
    #
    cS
    wcel
    #
    va
    cK
    wral
    #
    wa
    #
    wph
    @0
    wa
    #
    @3
    @8
    @10
    cS
    cT
    cF
    wph
    cS
    csiga
    crn
    cuni
    #
    wcel
    #
    @0
    imambfm.2
    adantr
    wph
    cT
    @11
    wcel
    #
    @0
    wph
    cT
    cK
    csigagen
    cfv
    #
    @11
    imambfm.3
    wph
    cK
    cvv
    imambfm.1
    sgsiga
    eqeltrd
    #
    adantr
    wph
    @0
    simpr
    mbfmf
    @10
    @7
    va
    cK
    @10
    @5
    cK
    wcel
    #
    wa
    #
    @5
    cS
    cT
    cF
    wph
    @12
    @0
    @16
    imambfm.2
    ad2antrr
    wph
    @13
    @0
    @16
    @15
    ad2antrr
    wph
    @0
    @16
    simplr
    @17
    cK
    cT
    @5
    wph
    cK
    cT
    wss
    #
    @0
    @16
    wph
    cK
    @14
    cT
    wph
    cK
    cvv
    wcel
    #
    cK
    @14
    wss
    imambfm.1
    cK
    cvv
    sssigagen
    syl
    imambfm.3
    sseqtr4d
    #
    ad2antrr
    @10
    @16
    simpr
    sseldd
    mbfmcnvima
    ralrimiva
    jca
    wph
    @9
    wa
    #
    @0
    cF
    @2
    @1
    cmap
    co
    wcel
    #
    @7
    va
    cT
    wral
    #
    @21
    @2
    cT
    wcel
    #
    @1
    cS
    wcel
    #
    @3
    @22
    wph
    @24
    @9
    wph
    @13
    @24
    @15
    cT
    unielsiga
    #
    syl
    adantr
    #
    wph
    @25
    @9
    wph
    @12
    @25
    imambfm.2
    cS
    unielsiga
    #
    syl
    adantr
    #
    wph
    @3
    @8
    simprl
    @24
    @25
    wa
    @22
    @3
    @2
    @1
    cF
    cT
    cS
    elmapg
    biimpar
    syl21anc
    @21
    cT
    @7
    va
    cT
    crab
    #
    wceq
    @23
    @21
    cT
    @30
    @21
    cT
    @14
    @30
    wph
    cT
    @14
    wceq
    @9
    imambfm.3
    adantr
    @21
    @30
    cK
    cuni
    #
    csiga
    cfv
    #
    wcel
    #
    cK
    @30
    wss
    #
    @14
    @30
    wss
    @21
    @30
    @2
    csiga
    cfv
    #
    wcel
    #
    @33
    @21
    wph
    @30
    @2
    cpw
    #
    wss
    #
    @2
    @30
    wcel
    #
    @2
    vx
    cv
    #
    cdif
    #
    @30
    wcel
    #
    vx
    @30
    wral
    #
    @40
    com
    cdom
    wbr
    #
    @40
    cuni
    #
    @30
    wcel
    #
    wi
    #
    vx
    @30
    cpw
    #
    wral
    #
    w3a
    #
    @36
    wph
    @9
    simpl
    @38
    @21
    @30
    cT
    @37
    @7
    va
    cT
    ssrab2
    #
    cT
    pwuni
    sstri
    a1i
    @21
    @39
    @43
    @49
    @21
    @24
    @4
    @2
    cima
    #
    cS
    wcel
    #
    @39
    @27
    @21
    @52
    @1
    cS
    @3
    @52
    @1
    wceq
    wph
    @8
    @1
    @2
    cF
    fimacnv
    ad2antrl
    #
    @29
    eqeltrd
    @7
    @53
    va
    @2
    cT
    @5
    @2
    wceq
    @6
    @52
    cS
    @5
    @2
    @4
    imaeq2
    eleq1d
    elrab
    sylanbrc
    @21
    @42
    vx
    @30
    @21
    @40
    @30
    wcel
    #
    wa
    #
    @41
    cT
    wcel
    #
    @4
    @41
    cima
    #
    cS
    wcel
    #
    @42
    @56
    @13
    @24
    @40
    cT
    wcel
    #
    @57
    wph
    @13
    @9
    @55
    @15
    ad2antrr
    #
    @56
    @13
    @24
    @61
    @26
    syl
    @55
    @60
    @21
    @7
    va
    @40
    cT
    elrabi
    adantl
    @2
    @40
    cT
    difelsiga
    syl3anc
    @56
    @58
    @52
    @4
    @40
    cima
    #
    cdif
    #
    cS
    @56
    @3
    cF
    wfun
    #
    @58
    @63
    wceq
    wph
    @3
    @8
    @55
    simplrl
    @1
    @2
    cF
    ffun
    #
    @2
    @40
    cF
    difpreima
    3syl
    @56
    @63
    @1
    @62
    cdif
    #
    cS
    @21
    @63
    @66
    wceq
    @55
    @21
    @52
    @1
    @62
    @54
    difeq1d
    adantr
    @56
    @12
    @25
    @62
    cS
    wcel
    #
    @66
    cS
    wcel
    wph
    @12
    @9
    @55
    imambfm.2
    ad2antrr
    #
    @56
    @12
    @25
    @68
    @28
    syl
    @55
    @67
    @21
    @55
    @60
    @67
    @7
    @67
    va
    @40
    cT
    @5
    @40
    wceq
    @6
    @62
    cS
    @5
    @40
    @4
    imaeq2
    eleq1d
    elrab
    simprbi
    adantl
    @1
    @62
    cS
    difelsiga
    syl3anc
    eqeltrd
    eqeltrd
    @7
    @59
    va
    @41
    cT
    @5
    @41
    wceq
    @6
    @58
    cS
    @5
    @41
    @4
    imaeq2
    eleq1d
    elrab
    sylanbrc
    ralrimiva
    @21
    @47
    vx
    @48
    @21
    @40
    @48
    wcel
    #
    wa
    #
    @44
    @46
    @70
    @44
    wa
    #
    @45
    cT
    wcel
    #
    @4
    @45
    cima
    #
    cS
    wcel
    #
    @46
    @71
    @13
    @40
    cT
    cpw
    #
    wcel
    #
    @44
    @72
    wph
    @13
    @9
    @69
    @44
    @15
    ad3antrrr
    @69
    @76
    @21
    @44
    @48
    @75
    @40
    @30
    cT
    wss
    #
    @48
    @75
    wss
    @51
    @30
    cT
    sspwb
    mpbi
    sseli
    ad2antlr
    @70
    @44
    simpr
    #
    @40
    cT
    sigaclcu
    syl3anc
    @71
    @73
    vy
    @40
    @4
    vy
    cv
    #
    cima
    #
    ciun
    #
    cS
    @71
    @3
    @64
    @73
    @81
    wceq
    @71
    @3
    @8
    wph
    @9
    @69
    @44
    simpllr
    simpld
    @65
    vy
    @40
    cF
    unipreima
    3syl
    @71
    @12
    @80
    cS
    wcel
    #
    vy
    @40
    wral
    @44
    @81
    cS
    wcel
    wph
    @12
    @9
    @69
    @44
    imambfm.2
    ad3antrrr
    @71
    @82
    vy
    @40
    @71
    @79
    @40
    wcel
    #
    wa
    #
    @79
    @30
    wcel
    #
    @82
    @84
    @83
    @69
    @85
    @71
    @83
    simpr
    @21
    @69
    @44
    @83
    simpllr
    @79
    @40
    @30
    elelpwi
    syl2anc
    @85
    @79
    cT
    wcel
    @82
    @7
    @82
    va
    @79
    cT
    @5
    @79
    wceq
    @6
    @80
    cS
    @5
    @79
    @4
    imaeq2
    eleq1d
    elrab
    simprbi
    syl
    ralrimiva
    @78
    @40
    @80
    cS
    vy
    vy
    @40
    nfcv
    sigaclcuni
    syl3anc
    eqeltrd
    @7
    @74
    va
    @45
    cT
    @5
    @45
    wceq
    @6
    @73
    cS
    @5
    @45
    @4
    imaeq2
    eleq1d
    elrab
    sylanbrc
    ex
    ralrimiva
    3jca
    wph
    @36
    @38
    @50
    wa
    #
    wph
    @13
    @30
    cvv
    wcel
    @36
    @86
    wb
    @15
    @7
    va
    cT
    @11
    rabexg
    vx
    @30
    @2
    issiga
    3syl
    biimpar
    syl12anc
    wph
    @36
    @33
    wb
    @9
    wph
    @35
    @32
    @30
    wph
    @2
    @31
    csiga
    wph
    @2
    @14
    cuni
    #
    @31
    wph
    cT
    @14
    imambfm.3
    unieqd
    wph
    @19
    @87
    @31
    wceq
    imambfm.1
    cK
    cvv
    unisg
    syl
    eqtrd
    fveq2d
    eleq2d
    adantr
    mpbid
    @21
    @18
    @8
    @34
    wph
    @18
    @9
    @20
    adantr
    wph
    @3
    @8
    simprr
    @7
    va
    cT
    cK
    ssrab
    sylanbrc
    cK
    @30
    sigagenss
    syl2anc
    eqsstrd
    @77
    @21
    @51
    a1i
    eqssd
    @7
    va
    cT
    rabid2
    sylib
    @21
    va
    cS
    cT
    cF
    wph
    @12
    @9
    imambfm.2
    adantr
    wph
    @13
    @9
    @15
    adantr
    ismbfm
    mpbir2and
    impbida
end
