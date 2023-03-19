include "ccph.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccl.mm"
include "cfv.mm"
include "ctop.mm"
include "cuni.mm"
include "ctopon.mm"
include "ctps.mm"
include "cngp.mm"
include "cphngp.mm"
include "ngptps.mm"
include "syl.mm"
include "adantr.mm"
include "istps.mm"
include "sylib.mm"
include "topontop.mm"
include "simpr.mm"
include "wceq.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "eqid.mm"
include "sscls.mm"
include "syl2anc.mm"
include "ocv2ss.mm"
include "cv.mm"
include "cip.mm"
include "co.mm"
include "csca.mm"
include "c0g.mm"
include "wral.mm"
include "clsss3.mm"
include "sseqtr4d.mm"
include "ocvss.mm"
include "a1i.mm"
include "sselda.mm"
include "crab.mm"
include "ccld.mm"
include "cin.mm"
include "cab.mm"
include "df-ss.mm"
include "ineq1d.mm"
include "dfrab3.mm"
include "ineq2i.mm"
include "inass.mm"
include "eqtr4i.mm"
include "3eqtr4g.mm"
include "clscld.mm"
include "cmpt.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cvv.mm"
include "fvex.mm"
include "mptiniseg.mm"
include "ax-mp.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "ccn.mm"
include "simpll.mm"
include "cnmptc.mm"
include "cnmptid.mm"
include "cnmpt1ip.mm"
include "cha.mm"
include "cc.mm"
include "cnfldhaus.mm"
include "cc0.mm"
include "cclm.mm"
include "cphclm.mm"
include "clm0.mm"
include "ad2antrr.mm"
include "0cn.mm"
include "syl6eqelr.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "sncld.mm"
include "sylancr.mm"
include "cnclima.mm"
include "syl5eqelr.mm"
include "incld.mm"
include "eqeltrrd.mm"
include "ocvi.mm"
include "ralrimiva.mm"
include "adantl.mm"
include "ssrab.mm"
include "sylanbrc.mm"
include "clsss2.mm"
include "ssrab2.mm"
include "eqssd.mm"
include "rabid2.mm"
include "elocv.mm"
include "syl3anbrc.mm"
include "ex.mm"
include "ssrdv.mm"

theorem clsocv
  let cS: class S
  let cJ: class J
  let cO: class O
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume clsocv.v: |- V = ( Base ` W )
  assume clsocv.o: |- O = ( ocv ` W )
  assume clsocv.j: |- J = ( TopOpen ` W )


  assert |- ( ( W e. CPreHil /\ S C_ V ) -> ( O ` ( ( cls ` J ) ` S ) ) = ( O ` S ) )

  proof
    cW
    ccph
    wcel
    #
    cS
    cV
    wss
    #
    wa
    #
    cS
    cJ
    ccl
    cfv
    cfv
    #
    cO
    cfv
    #
    cS
    cO
    cfv
    #
    @2
    cS
    @3
    wss
    #
    @4
    @5
    wss
    @2
    cJ
    ctop
    wcel
    #
    cS
    cJ
    cuni
    #
    wss
    #
    @6
    @2
    cJ
    cV
    ctopon
    cfv
    wcel
    #
    @7
    @2
    cW
    ctps
    wcel
    #
    @10
    @0
    @11
    @1
    @0
    cW
    cngp
    wcel
    @11
    cW
    cphngp
    cW
    ngptps
    syl
    adantr
    cV
    cJ
    cW
    clsocv.v
    clsocv.j
    istps
    sylib
    #
    cV
    cJ
    topontop
    syl
    #
    @2
    cS
    cV
    @8
    @0
    @1
    simpr
    @2
    @10
    cV
    @8
    wceq
    @12
    cV
    cJ
    toponuni
    syl
    #
    sseqtrd
    #
    cS
    cJ
    @8
    @8
    eqid
    #
    sscls
    syl2anc
    #
    @3
    cS
    cO
    cW
    clsocv.o
    ocv2ss
    syl
    @2
    vx
    @5
    @4
    @2
    vx
    cv
    #
    @5
    wcel
    #
    @18
    @4
    wcel
    #
    @2
    @19
    wa
    #
    @3
    cV
    wss
    #
    @18
    cV
    wcel
    @18
    vy
    cv
    #
    cW
    cip
    cfv
    #
    co
    #
    cW
    csca
    cfv
    #
    c0g
    cfv
    #
    wceq
    #
    vy
    @3
    wral
    #
    @20
    @2
    @22
    @19
    @2
    @3
    @8
    cV
    @2
    @7
    @9
    @3
    @8
    wss
    @13
    @15
    cS
    cJ
    @8
    @16
    clsss3
    syl2anc
    @14
    sseqtr4d
    adantr
    #
    @2
    @5
    cV
    @18
    @5
    cV
    wss
    @2
    cS
    cO
    cV
    cW
    clsocv.v
    clsocv.o
    ocvss
    a1i
    sselda
    #
    @21
    @3
    @28
    vy
    @3
    crab
    #
    wceq
    @29
    @21
    @3
    @32
    @21
    @32
    cJ
    ccld
    cfv
    #
    wcel
    cS
    @32
    wss
    #
    @3
    @32
    wss
    @21
    @3
    @28
    vy
    cV
    crab
    #
    cin
    #
    @32
    @33
    @21
    @3
    cV
    cin
    #
    @28
    vy
    cab
    #
    cin
    #
    @3
    @38
    cin
    @36
    @32
    @21
    @37
    @3
    @38
    @21
    @22
    @37
    @3
    wceq
    @30
    @3
    cV
    df-ss
    sylib
    ineq1d
    @36
    @3
    cV
    @38
    cin
    #
    cin
    @39
    @35
    @40
    @3
    @28
    vy
    cV
    dfrab3
    ineq2i
    @3
    cV
    @38
    inass
    eqtr4i
    @28
    vy
    @3
    dfrab3
    3eqtr4g
    @21
    @3
    @33
    wcel
    #
    @35
    @33
    wcel
    @36
    @33
    wcel
    @2
    @41
    @19
    @2
    @7
    @9
    @41
    @13
    @15
    cS
    cJ
    @8
    @16
    clscld
    syl2anc
    adantr
    @21
    @35
    vy
    cV
    @25
    cmpt
    #
    ccnv
    @27
    csn
    #
    cima
    #
    @33
    @27
    cvv
    wcel
    @44
    @35
    wceq
    @26
    c0g
    fvex
    vy
    cV
    @25
    @27
    @42
    cvv
    @42
    eqid
    mptiniseg
    ax-mp
    @21
    @42
    cJ
    ccnfld
    ctopn
    cfv
    #
    ccn
    co
    wcel
    @43
    @45
    ccld
    cfv
    wcel
    #
    @44
    @33
    wcel
    @21
    vy
    @18
    @23
    @45
    @24
    cJ
    cJ
    cW
    cV
    clsocv.j
    @45
    eqid
    #
    @24
    eqid
    #
    @0
    @1
    @19
    simpll
    @2
    @10
    @19
    @12
    adantr
    #
    @21
    vy
    @18
    cJ
    cJ
    cV
    cV
    @49
    @49
    @31
    cnmptc
    @21
    vy
    cJ
    cV
    @49
    cnmptid
    cnmpt1ip
    @21
    @45
    cha
    wcel
    @27
    cc
    wcel
    @46
    @45
    @47
    cnfldhaus
    @21
    @27
    cc0
    cc
    @0
    cc0
    @27
    wceq
    #
    @1
    @19
    @0
    cW
    cclm
    wcel
    @50
    cW
    cphclm
    @26
    cW
    @26
    eqid
    #
    clm0
    syl
    ad2antrr
    0cn
    syl6eqelr
    @27
    @45
    cc
    cc
    @45
    @45
    @47
    cnfldtopon
    toponunii
    sncld
    sylancr
    @43
    @42
    cJ
    @45
    cnclima
    syl2anc
    syl5eqelr
    @3
    @35
    cJ
    incld
    syl2anc
    eqeltrrd
    @21
    @6
    @28
    vy
    cS
    wral
    #
    @34
    @2
    @6
    @19
    @17
    adantr
    @19
    @52
    @2
    @19
    @28
    vy
    cS
    @18
    @23
    cS
    @26
    @24
    cO
    cV
    cW
    @27
    clsocv.v
    @48
    @51
    @27
    eqid
    #
    clsocv.o
    ocvi
    ralrimiva
    adantl
    @28
    vy
    @3
    cS
    ssrab
    sylanbrc
    @32
    cS
    cJ
    @8
    @16
    clsss2
    syl2anc
    @32
    @3
    wss
    @21
    @28
    vy
    @3
    ssrab2
    a1i
    eqssd
    @28
    vy
    @3
    rabid2
    sylib
    vy
    @18
    @3
    @26
    @24
    cO
    cV
    cW
    @27
    clsocv.v
    @48
    @51
    @53
    clsocv.o
    elocv
    syl3anbrc
    ex
    ssrdv
    eqssd
end
