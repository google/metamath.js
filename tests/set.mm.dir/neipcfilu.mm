include "cusp.mm"
include "wcel.mm"
include "ctps.mm"
include "w3a.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "ccfilu.mm"
include "cfbas.mm"
include "cv.mm"
include "cxp.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "cfil.mm"
include "ctopon.mm"
include "c0.mm"
include "wne.mm"
include "simp2.mm"
include "istps.mm"
include "sylib.mm"
include "simp3.mm"
include "snssd.mm"
include "snnzg.mm"
include "syl.mm"
include "neifil.mm"
include "syl3anc.mm"
include "filfbas.mm"
include "wa.mm"
include "cima.mm"
include "cutop.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "eqid.mm"
include "imaeq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "imaex.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "ad2antlr.mm"
include "cust.mm"
include "isusp.mm"
include "simplbi.mm"
include "3ad2ant1.mm"
include "utopsnneip.mm"
include "syl2anc.mm"
include "eleq2d.mm"
include "ad3antrrr.mm"
include "mpbird.mm"
include "simpl1.mm"
include "3anassrs.mm"
include "simprbi.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "eleqtrrd.mm"
include "simpr.mm"
include "id.mm"
include "sqxpeqd.mm"
include "sseq1d.mm"
include "adantr.mm"
include "ccom.mm"
include "ccnv.mm"
include "simpll1.mm"
include "simplr.mm"
include "ustexsym.mm"
include "ad2antrr.mm"
include "ustssxp.mm"
include "simpll2.mm"
include "ustneism.mm"
include "simprl.mm"
include "coeq2d.mm"
include "coss1.mm"
include "coss2.mm"
include "sstrd.mm"
include "ad2antll.mm"
include "simpllr.mm"
include "eqsstrd.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "ustexhalf.mm"
include "3adant2.mm"
include "r19.29a.mm"
include "ralrimiva.mm"
include "iscfilu.mm"
include "mpbir2and.mm"

theorem neipcfilu
  let cP: class P
  let cU: class U
  let cJ: class J
  let cW: class W
  let cX: class X
  let va: setvar a
  let vv: setvar v
  let vw: setvar w
  let vu: setvar u
  assume neipcfilu.x: |- X = ( Base ` W )
  assume neipcfilu.j: |- J = ( TopOpen ` W )
  assume neipcfilu.u: |- U = ( UnifSt ` W )


  assert |- ( ( W e. UnifSp /\ W e. TopSp /\ P e. X ) -> ( ( nei ` J ) ` { P } ) e. ( CauFilU ` U ) )

  proof
    cW
    cusp
    wcel
    #
    cW
    ctps
    wcel
    #
    cP
    cX
    wcel
    #
    w3a
    #
    cP
    csn
    #
    cJ
    cnei
    cfv
    #
    cfv
    #
    cU
    ccfilu
    cfv
    wcel
    #
    @6
    cX
    cfbas
    cfv
    wcel
    #
    va
    cv
    #
    @9
    cxp
    #
    vv
    cv
    #
    wss
    #
    va
    @6
    wrex
    #
    vv
    cU
    wral
    #
    @3
    @6
    cX
    cfil
    cfv
    wcel
    #
    @8
    @3
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @4
    cX
    wss
    @4
    c0
    wne
    #
    @15
    @3
    @1
    @16
    @0
    @1
    @2
    simp2
    cX
    cJ
    cW
    neipcfilu.x
    neipcfilu.j
    istps
    sylib
    @3
    cP
    cX
    @0
    @1
    @2
    simp3
    #
    snssd
    @3
    @2
    @17
    @18
    cP
    cX
    snnzg
    syl
    @4
    cJ
    cX
    neifil
    syl3anc
    @6
    cX
    filfbas
    syl
    @3
    @13
    vv
    cU
    @3
    @11
    cU
    wcel
    #
    wa
    #
    vw
    cv
    #
    @4
    cima
    #
    @22
    cxp
    #
    @11
    wss
    #
    @13
    vw
    cU
    @20
    @21
    cU
    wcel
    #
    wa
    #
    @24
    wa
    #
    @22
    @6
    wcel
    @24
    @13
    @27
    @22
    @4
    cU
    cutop
    cfv
    #
    cnei
    cfv
    #
    cfv
    #
    @6
    @27
    @22
    @30
    wcel
    #
    @22
    vv
    cU
    @11
    @4
    cima
    #
    cmpt
    #
    crn
    #
    wcel
    #
    @25
    @35
    @20
    @24
    @25
    @22
    @32
    wceq
    #
    vv
    cU
    wrex
    #
    @35
    @25
    @22
    @22
    wceq
    #
    @37
    @22
    eqid
    @36
    @38
    vv
    @21
    cU
    @11
    @21
    wceq
    @32
    @22
    @22
    @11
    @21
    @4
    imaeq1
    eqeq2d
    rspcev
    mpan2
    @22
    cvv
    wcel
    @35
    @37
    wb
    @21
    @4
    vw
    vex
    imaex
    vv
    cU
    @32
    @22
    @33
    cvv
    @33
    eqid
    elrnmpt
    ax-mp
    sylibr
    ad2antlr
    @3
    @31
    @35
    wb
    @19
    @25
    @24
    @3
    @30
    @34
    @22
    @3
    cU
    cX
    cust
    cfv
    wcel
    #
    @2
    @30
    @34
    wceq
    @0
    @1
    @39
    @2
    @0
    @39
    cJ
    @28
    wceq
    #
    cX
    cU
    cJ
    cW
    neipcfilu.x
    neipcfilu.u
    neipcfilu.j
    isusp
    #
    simplbi
    3ad2ant1
    #
    @18
    vv
    cP
    cU
    @28
    cX
    @28
    eqid
    utopsnneip
    syl2anc
    eleq2d
    ad3antrrr
    mpbird
    @27
    @4
    @5
    @29
    @27
    cJ
    @28
    cnei
    @27
    @0
    @40
    @3
    @19
    @25
    @24
    @0
    @0
    @1
    @2
    @19
    @25
    @24
    w3a
    simpl1
    3anassrs
    @0
    @39
    @40
    @41
    simprbi
    syl
    fveq2d
    fveq1d
    eleqtrrd
    @26
    @24
    simpr
    @12
    @24
    va
    @22
    @6
    @9
    @22
    wceq
    #
    @10
    @23
    @11
    @43
    @9
    @22
    @43
    id
    sqxpeqd
    sseq1d
    rspcev
    syl2anc
    @20
    @39
    @2
    @19
    @24
    vw
    cU
    wrex
    #
    @3
    @39
    @19
    @42
    adantr
    @3
    @2
    @19
    @18
    adantr
    @3
    @19
    simpr
    @39
    @2
    @19
    w3a
    #
    vu
    cv
    #
    @46
    ccom
    #
    @11
    wss
    #
    @44
    vu
    cU
    @45
    @46
    cU
    wcel
    #
    wa
    #
    @48
    wa
    #
    @21
    ccnv
    #
    @21
    wceq
    #
    @21
    @46
    wss
    #
    wa
    #
    vw
    cU
    wrex
    #
    @44
    @51
    @39
    @49
    @56
    @39
    @2
    @19
    @49
    @48
    simpll1
    #
    @45
    @49
    @48
    simplr
    vw
    cU
    @46
    cX
    ustexsym
    syl2anc
    @51
    @55
    @24
    vw
    cU
    @51
    @25
    wa
    #
    @55
    @24
    @58
    @55
    wa
    #
    @23
    @21
    @52
    ccom
    #
    @11
    @59
    @21
    cX
    cX
    cxp
    wss
    #
    @2
    @23
    @60
    wss
    @59
    @39
    @25
    @61
    @51
    @39
    @25
    @55
    @57
    ad2antrr
    @51
    @25
    @55
    simplr
    cU
    @21
    cX
    ustssxp
    syl2anc
    @50
    @48
    @25
    @55
    @2
    @39
    @2
    @19
    @49
    @48
    @25
    @55
    w3a
    simpll2
    3anassrs
    cP
    @21
    cX
    ustneism
    syl2anc
    @59
    @60
    @21
    @21
    ccom
    #
    @11
    @59
    @52
    @21
    @21
    @58
    @53
    @54
    simprl
    coeq2d
    @59
    @62
    @47
    @11
    @54
    @62
    @47
    wss
    @58
    @53
    @54
    @62
    @46
    @21
    ccom
    @47
    @21
    @46
    @21
    coss1
    @21
    @46
    @46
    coss2
    sstrd
    ad2antll
    @50
    @48
    @25
    @55
    simpllr
    sstrd
    eqsstrd
    sstrd
    ex
    reximdva
    mpd
    @39
    @19
    @48
    vu
    cU
    wrex
    @2
    vu
    cU
    @11
    cX
    ustexhalf
    3adant2
    r19.29a
    syl3anc
    r19.29a
    ralrimiva
    @3
    @39
    @7
    @8
    @14
    wa
    wb
    @42
    vv
    cU
    @6
    cX
    va
    iscfilu
    syl
    mpbir2and
end
