include "cfv.mm"
include "cpnf.mm"
include "wceq.mm"
include "csumge0.mm"
include "wa.mm"
include "cvv.mm"
include "csn.mm"
include "wcel.mm"
include "snex.mm"
include "a1i.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "adantr.mm"
include "crn.mm"
include "id.mm"
include "eqcomd.mm"
include "adantl.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "syl.mm"
include "snidg.mm"
include "fdm.mm"
include "eleqtrd.mm"
include "fvelrn.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "sge0pnfval.mm"
include "simpr.mm"
include "eqtr4d.mm"
include "wn.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "csu.mm"
include "cmpt.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "elsni.mm"
include "con3i.mm"
include "rnsnf.mm"
include "neleqtrd.mm"
include "fge0iccico.mm"
include "sge0reval.mm"
include "cpr.mm"
include "c0.mm"
include "sum0.mm"
include "eqcomi.mm"
include "nfcvd.mm"
include "nfv.mm"
include "fveq2.mm"
include "cico.mm"
include "cc.mm"
include "cr.mm"
include "rge0ssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "ffvelrnd.mm"
include "sseldi.mm"
include "sumsnd.mm"
include "preq12d.mm"
include "supeq1d.mm"
include "wbr.mm"
include "cif.mm"
include "wor.mm"
include "xrltso.mm"
include "0xr.mm"
include "iccssxr.mm"
include "suppr.mm"
include "syl3anc.mm"
include "cle.mm"
include "w3a.mm"
include "pnfxr.mm"
include "3jca.mm"
include "iccgelb.mm"
include "xrlenltd.mm"
include "mpbid.mm"
include "iffalsed.mm"
include "eqtr2d.mm"
include "cop.mm"
include "pwsn.mm"
include "ineq1i.mm"
include "wss.mm"
include "0fin.mm"
include "snfi.mm"
include "prssi.mm"
include "mp2an.mm"
include "df-ss.mm"
include "biimpi.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "mpteq1.mm"
include "wtru.mm"
include "0ex.mm"
include "sumex.mm"
include "sumeq1.mm"
include "fmptpr.mm"
include "trud.mm"
include "rneqi.mm"
include "rnpropg.mm"
include "supeq1i.mm"
include "3eqtr4d.mm"
include "pm2.61dan.mm"

theorem sge0sn
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume sge0sn.1: |- ( ph -> A e. V )
  assume sge0sn.2: |- ( ph -> F : { A } --> ( 0 [,] +oo ) )


  assert |- ( ph -> ( sum^ ` F ) = ( F ` A ) )

  proof
    wph
    cA
    cF
    cfv
    #
    cpnf
    wceq
    #
    cF
    csumge0
    cfv
    #
    @0
    wceq
    wph
    @1
    wa
    #
    @2
    cpnf
    @0
    @3
    cF
    cvv
    cA
    csn
    #
    @4
    cvv
    wcel
    #
    @3
    cA
    snex
    #
    a1i
    wph
    @4
    cc0
    cpnf
    cicc
    co
    #
    cF
    wf
    #
    @1
    sge0sn.2
    adantr
    @3
    cpnf
    @0
    cF
    crn
    #
    @1
    cpnf
    @0
    wceq
    wph
    @1
    @0
    cpnf
    @1
    id
    eqcomd
    adantl
    @3
    cF
    wfun
    #
    cA
    cF
    cdm
    #
    wcel
    #
    @0
    @9
    wcel
    wph
    @10
    @1
    wph
    @8
    @10
    sge0sn.2
    @4
    @7
    cF
    ffun
    syl
    adantr
    wph
    @12
    @1
    wph
    cA
    @4
    @11
    wph
    cA
    cV
    wcel
    #
    cA
    @4
    wcel
    #
    sge0sn.1
    cA
    cV
    snidg
    #
    syl
    #
    wph
    @11
    @4
    wph
    @8
    @11
    @4
    wceq
    sge0sn.2
    @4
    @7
    cF
    fdm
    syl
    eqcomd
    eleqtrd
    adantr
    cA
    cF
    fvelrn
    syl2anc
    eqeltrd
    sge0pnfval
    wph
    @1
    simpr
    eqtr4d
    wph
    @1
    wn
    #
    wa
    #
    @2
    vx
    @4
    cpw
    #
    cfn
    cin
    #
    vx
    cv
    #
    vy
    cv
    #
    cF
    cfv
    #
    vy
    csu
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    @0
    @18
    vx
    vy
    cF
    cvv
    @4
    @5
    @18
    @6
    a1i
    @18
    cF
    @4
    wph
    @8
    @17
    sge0sn.2
    adantr
    @18
    @0
    csn
    #
    @9
    cpnf
    @17
    cpnf
    @28
    wcel
    #
    wn
    wph
    @29
    @1
    @29
    cpnf
    @0
    cpnf
    @0
    elsni
    eqcomd
    con3i
    adantl
    wph
    @28
    @9
    wceq
    @17
    wph
    @9
    @28
    wph
    cA
    @7
    cF
    cV
    sge0sn.1
    sge0sn.2
    rnsnf
    eqcomd
    adantr
    neleqtrd
    fge0iccico
    #
    sge0reval
    @18
    cc0
    @0
    cpr
    #
    cxr
    clt
    csup
    #
    c0
    @23
    vy
    csu
    #
    @4
    @23
    vy
    csu
    #
    cpr
    #
    cxr
    clt
    csup
    #
    @0
    @27
    @18
    cxr
    @31
    @35
    clt
    @18
    cc0
    @33
    @0
    @34
    cc0
    @33
    wceq
    @18
    @33
    cc0
    @23
    vy
    sum0
    eqcomi
    a1i
    @18
    @34
    @0
    @18
    @23
    @0
    vy
    cA
    cV
    @18
    vy
    @0
    nfcvd
    @18
    vy
    nfv
    @22
    cA
    wceq
    @23
    @0
    wceq
    @18
    @22
    cA
    cF
    fveq2
    adantl
    wph
    @13
    @17
    sge0sn.1
    adantr
    #
    @18
    cc0
    cpnf
    cico
    co
    #
    cc
    @0
    @38
    cr
    cc
    rge0ssre
    ax-resscn
    sstri
    @18
    @4
    @38
    cA
    cF
    @30
    @18
    @13
    @14
    @37
    @15
    syl
    ffvelrnd
    sseldi
    sumsnd
    eqcomd
    preq12d
    supeq1d
    wph
    @0
    @32
    wceq
    @17
    wph
    @32
    @0
    cc0
    clt
    wbr
    #
    cc0
    @0
    cif
    #
    @0
    wph
    cxr
    clt
    wor
    #
    cc0
    cxr
    wcel
    #
    @0
    cxr
    wcel
    @32
    @40
    wceq
    @41
    wph
    xrltso
    a1i
    @42
    wph
    0xr
    a1i
    #
    wph
    @7
    cxr
    @0
    cc0
    cpnf
    iccssxr
    wph
    @4
    @7
    cA
    cF
    sge0sn.2
    @16
    ffvelrnd
    #
    sseldi
    #
    cxr
    cc0
    @0
    clt
    suppr
    syl3anc
    wph
    @39
    cc0
    @0
    wph
    cc0
    @0
    cle
    wbr
    #
    @39
    wn
    wph
    @42
    cpnf
    cxr
    wcel
    #
    @0
    @7
    wcel
    #
    w3a
    @46
    wph
    @42
    @47
    @48
    @43
    @47
    wph
    pnfxr
    a1i
    @44
    3jca
    cc0
    cpnf
    @0
    iccgelb
    syl
    wph
    cc0
    @0
    @43
    @45
    xrlenltd
    mpbid
    iffalsed
    eqtr2d
    adantr
    @27
    @36
    wceq
    @18
    cxr
    @26
    @35
    clt
    @26
    c0
    @33
    cop
    @4
    @34
    cop
    cpr
    #
    crn
    #
    @35
    @25
    @49
    @25
    vx
    c0
    @4
    cpr
    #
    @24
    cmpt
    #
    @49
    @20
    @51
    wceq
    @25
    @52
    wceq
    @20
    @51
    cfn
    cin
    #
    @51
    @19
    @51
    cfn
    cA
    pwsn
    ineq1i
    @51
    cfn
    wss
    #
    @53
    @51
    wceq
    #
    c0
    cfn
    wcel
    @4
    cfn
    wcel
    @54
    0fin
    cA
    snfi
    c0
    @4
    cfn
    prssi
    mp2an
    @54
    @55
    @51
    cfn
    df-ss
    biimpi
    ax-mp
    eqtri
    vx
    @20
    @51
    @24
    mpteq1
    ax-mp
    @49
    @52
    @49
    @52
    wceq
    wtru
    vx
    c0
    @4
    @33
    @34
    @24
    cvv
    cvv
    cvv
    cvv
    c0
    cvv
    wcel
    #
    wtru
    0ex
    a1i
    @5
    wtru
    @6
    a1i
    @33
    cvv
    wcel
    wtru
    c0
    @23
    vy
    sumex
    a1i
    @34
    cvv
    wcel
    wtru
    @4
    @23
    vy
    sumex
    a1i
    @21
    c0
    wceq
    @24
    @33
    wceq
    wtru
    @21
    c0
    @23
    vy
    sumeq1
    adantl
    @21
    @4
    wceq
    @24
    @34
    wceq
    wtru
    @21
    @4
    @23
    vy
    sumeq1
    adantl
    fmptpr
    trud
    eqcomi
    eqtri
    rneqi
    @56
    @5
    @50
    @35
    wceq
    0ex
    @6
    c0
    @4
    @33
    @34
    cvv
    cvv
    rnpropg
    mp2an
    eqtri
    supeq1i
    a1i
    3eqtr4d
    eqtr4d
    pm2.61dan
end
