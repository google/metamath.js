include "c0.mm"
include "cfv.mm"
include "coms.mm"
include "cc0.mm"
include "fveq1i.mm"
include "cv.mm"
include "cuni.mm"
include "wss.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "cdm.mm"
include "cpw.mm"
include "crab.mm"
include "cesum.mm"
include "cmpt.mm"
include "crn.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "clt.mm"
include "cinf.mm"
include "wcel.mm"
include "wf.mm"
include "wceq.mm"
include "0ss.mm"
include "fdm.mm"
include "syl.mm"
include "unieqd.mm"
include "syl5sseq.mm"
include "omsfval.mm"
include "syl3anc.mm"
include "wor.mm"
include "cxr.mm"
include "iccssxr.mm"
include "xrltso.mm"
include "soss.mm"
include "mp2.mm"
include "a1i.mm"
include "0e0iccpnf.mm"
include "wrex.mm"
include "csn.mm"
include "snssd.mm"
include "p0ex.mm"
include "elpw.mm"
include "sylibr.mm"
include "cvv.mm"
include "0ex.mm"
include "snct.mm"
include "ax-mp.mm"
include "pm3.2i.mm"
include "jctir.mm"
include "unieq.mm"
include "sseq2d.mm"
include "breq1.mm"
include "anbi12d.mm"
include "elrab.mm"
include "simpr.mm"
include "fveq2d.mm"
include "adantr.mm"
include "eqtrd.mm"
include "esumsn.mm"
include "eqcomd.mm"
include "esumeq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wb.mm"
include "0xr.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "wn.mm"
include "cle.mm"
include "nfv.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfcri.mm"
include "nfan.mm"
include "wral.mm"
include "vex.mm"
include "nfcv.mm"
include "nfesum1.mm"
include "nfmpt.mm"
include "nfeq2.mm"
include "ad4antr.mm"
include "ssrab2.mm"
include "simpllr.mm"
include "sseldi.mm"
include "pweqd.mm"
include "eleqtrd.mm"
include "elpwid.mm"
include "sseldd.mm"
include "ffvelrnd.mm"
include "ex.mm"
include "ralrimi.mm"
include "esumcl.mm"
include "sylancr.mm"
include "eqeltrd.mm"
include "biimpi.mm"
include "adantl.mm"
include "r19.29af.mm"
include "pnfxr.mm"
include "iccgelb.mm"
include "mp3an12.mm"
include "xrlenlt.mm"
include "bicomd.mm"
include "mpbird.mm"
include "infmin.mm"
include "syl5eq.mm"

theorem oms0
  let wph: wff ph
  let cQ: class Q
  let cR: class R
  let cM: class M
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  assume oms.m: |- M = ( toOMeas ` R )
  assume oms.o: |- ( ph -> Q e. V )
  assume oms.r: |- ( ph -> R : Q --> ( 0 [,] +oo ) )
  assume oms.d: |- ( ph -> (/) e. dom R )
  assume oms.0: |- ( ph -> ( R ` (/) ) = 0 )


  assert |- ( ph -> ( M ` (/) ) = 0 )

  proof
    wph
    c0
    cM
    cfv
    c0
    cR
    coms
    cfv
    #
    cfv
    #
    cc0
    c0
    cM
    @0
    oms.m
    fveq1i
    wph
    @1
    vx
    c0
    vz
    cv
    #
    cuni
    #
    wss
    #
    @2
    com
    cdom
    wbr
    #
    wa
    #
    vz
    cR
    cdm
    #
    cpw
    #
    crab
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    cfv
    #
    vy
    cesum
    #
    cmpt
    #
    crn
    #
    cc0
    cpnf
    cicc
    co
    #
    clt
    cinf
    #
    cc0
    wph
    cQ
    cV
    wcel
    cQ
    @16
    cR
    wf
    #
    c0
    cQ
    cuni
    #
    wss
    @1
    @17
    wceq
    oms.o
    oms.r
    wph
    @7
    cuni
    #
    c0
    @19
    @20
    0ss
    wph
    @7
    cQ
    wph
    @18
    @7
    cQ
    wceq
    oms.r
    cQ
    @16
    cR
    fdm
    syl
    #
    unieqd
    syl5sseq
    vx
    vy
    vz
    c0
    cQ
    cR
    cV
    omsfval
    syl3anc
    wph
    va
    @16
    @15
    cc0
    clt
    @16
    clt
    wor
    #
    wph
    @16
    cxr
    wss
    cxr
    clt
    wor
    @22
    cc0
    cpnf
    iccssxr
    #
    xrltso
    @16
    cxr
    clt
    soss
    mp2
    a1i
    cc0
    @16
    wcel
    wph
    0e0iccpnf
    a1i
    #
    wph
    cc0
    @13
    wceq
    #
    vx
    @9
    wrex
    #
    cc0
    @15
    wcel
    #
    wph
    c0
    csn
    #
    @9
    wcel
    #
    cc0
    @28
    @12
    vy
    cesum
    #
    wceq
    #
    @26
    wph
    @28
    @8
    wcel
    #
    c0
    @28
    cuni
    #
    wss
    #
    @28
    com
    cdom
    wbr
    #
    wa
    #
    wa
    @29
    wph
    @32
    @36
    wph
    @28
    @7
    wss
    @32
    wph
    c0
    @7
    oms.d
    snssd
    @28
    @7
    p0ex
    elpw
    sylibr
    @34
    @35
    @33
    0ss
    c0
    cvv
    wcel
    @35
    0ex
    c0
    cvv
    snct
    ax-mp
    pm3.2i
    jctir
    @6
    @36
    vz
    @28
    @8
    @2
    @28
    wceq
    #
    @4
    @34
    @5
    @35
    @37
    @3
    @33
    c0
    @2
    @28
    unieq
    sseq2d
    @2
    @28
    com
    cdom
    breq1
    anbi12d
    elrab
    sylibr
    wph
    @30
    cc0
    wph
    @12
    cc0
    vy
    c0
    @7
    wph
    @11
    c0
    wceq
    #
    wa
    #
    @12
    c0
    cR
    cfv
    #
    cc0
    @39
    @11
    c0
    cR
    wph
    @38
    simpr
    fveq2d
    wph
    @40
    cc0
    wceq
    @38
    oms.0
    adantr
    eqtrd
    oms.d
    @24
    esumsn
    eqcomd
    @25
    @31
    vx
    @28
    @9
    @10
    @28
    wceq
    @13
    @30
    cc0
    @10
    @28
    @12
    vy
    esumeq1
    eqeq2d
    rspcev
    syl2anc
    cc0
    cxr
    wcel
    #
    @27
    @26
    wb
    0xr
    vx
    @9
    @13
    cc0
    @14
    cxr
    @14
    eqid
    #
    elrnmpt
    ax-mp
    sylibr
    wph
    va
    cv
    #
    @15
    wcel
    #
    wa
    #
    @43
    cc0
    clt
    wbr
    wn
    #
    cc0
    @43
    cle
    wbr
    #
    @45
    @43
    @16
    wcel
    #
    @47
    @45
    @43
    @13
    wceq
    #
    @48
    vx
    @9
    wph
    @44
    vx
    wph
    vx
    nfv
    vx
    va
    @15
    vx
    @14
    vx
    @9
    @13
    nfmpt1
    nfrn
    nfcri
    nfan
    @45
    @10
    @9
    wcel
    #
    wa
    #
    @49
    wa
    #
    @43
    @13
    @16
    @51
    @49
    simpr
    @52
    @10
    cvv
    wcel
    @12
    @16
    wcel
    #
    vy
    @10
    wral
    @13
    @16
    wcel
    vx
    vex
    @52
    @53
    vy
    @10
    @51
    @49
    vy
    @45
    @50
    vy
    wph
    @44
    vy
    wph
    vy
    nfv
    vy
    va
    @15
    vy
    @14
    vy
    vx
    @9
    @13
    vy
    @9
    nfcv
    @10
    @12
    vy
    vy
    @10
    nfcv
    #
    nfesum1
    #
    nfmpt
    nfrn
    nfcri
    nfan
    @50
    vy
    nfv
    nfan
    vy
    @43
    @13
    @55
    nfeq2
    nfan
    @52
    @11
    @10
    wcel
    #
    @53
    @52
    @56
    wa
    #
    cQ
    @16
    @11
    cR
    wph
    @18
    @44
    @50
    @49
    @56
    oms.r
    ad4antr
    @57
    @10
    cQ
    @11
    @57
    @10
    cQ
    @57
    @10
    @8
    cQ
    cpw
    #
    @57
    @9
    @8
    @10
    @6
    vz
    @8
    ssrab2
    @45
    @50
    @49
    @56
    simpllr
    sseldi
    wph
    @8
    @58
    wceq
    @44
    @50
    @49
    @56
    wph
    @7
    cQ
    @21
    pweqd
    ad4antr
    eleqtrd
    elpwid
    @52
    @56
    simpr
    sseldd
    ffvelrnd
    ex
    ralrimi
    @10
    @12
    vy
    cvv
    @54
    esumcl
    sylancr
    eqeltrd
    @44
    @49
    vx
    @9
    wrex
    #
    wph
    @44
    @59
    @43
    cvv
    wcel
    @44
    @59
    wb
    va
    vex
    vx
    @9
    @13
    @43
    @14
    cvv
    @42
    elrnmpt
    ax-mp
    biimpi
    adantl
    r19.29af
    #
    @41
    cpnf
    cxr
    wcel
    @48
    @47
    0xr
    pnfxr
    cc0
    cpnf
    @43
    iccgelb
    mp3an12
    syl
    @45
    @41
    @43
    cxr
    wcel
    #
    @46
    @47
    wb
    0xr
    @45
    @16
    cxr
    @43
    @23
    @60
    sseldi
    @41
    @61
    wa
    @47
    @46
    cc0
    @43
    xrlenlt
    bicomd
    sylancr
    mpbird
    infmin
    eqtrd
    syl5eq
end
