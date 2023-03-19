include "cmeas.mm"
include "cfv.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cxdiv.mm"
include "cofc.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "cdm.mm"
include "ofcfval3.mm"
include "wceq.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "wf.mm"
include "measfrge0.mm"
include "fdm.mm"
include "syl.mm"
include "adantr.mm"
include "mpteq1d.mm"
include "eqtrd.mm"
include "c0.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "cuni.mm"
include "cesum.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "measvxrge0.mm"
include "adantlr.mm"
include "simplr.mm"
include "xrpxdivcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "cvv.mm"
include "csiga.mm"
include "crn.mm"
include "measbase.mm"
include "0elsiga.mm"
include "ovex.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "fvmptg.mm"
include "sylancl.mm"
include "measvnul.mm"
include "xdiv0rp.mm"
include "sylan9eq.mm"
include "simpll.mm"
include "simprl.mm"
include "simprr.mm"
include "w3a.mm"
include "vex.mm"
include "a1i.mm"
include "simplll.mm"
include "wss.mm"
include "selpw.mm"
include "ssel2.mm"
include "sylanb.mm"
include "adantll.mm"
include "syl2anc.mm"
include "esumdivc.mm"
include "3ad2antr1.mm"
include "ad2antrr.mm"
include "simpr1.mm"
include "simpr2.mm"
include "sigaclcu.mm"
include "syl3anc.mm"
include "fvmpt3i.mm"
include "simpr3.mm"
include "measvun.mm"
include "syl112anc.mm"
include "esumeq2dv.mm"
include "3eqtr4d.mm"
include "syl13anc.mm"
include "ex.mm"
include "ralrimiva.mm"
include "wb.mm"
include "ismeas.mm"
include "biimprd.mm"
include "mp3and.mm"
include "eqeltrd.mm"

theorem measdivcst
  let cA: class A
  let cS: class S
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( M e. ( measures ` S ) /\ A e. RR+ ) -> ( M oFC /e A ) e. ( measures ` S ) )

  proof
    cM
    cS
    cmeas
    cfv
    #
    wcel
    #
    cA
    crp
    wcel
    #
    wa
    #
    cM
    cA
    cxdiv
    cofc
    co
    #
    vx
    cS
    vx
    cv
    #
    cM
    cfv
    #
    cA
    cxdiv
    co
    #
    cmpt
    #
    @0
    @3
    @4
    vx
    cM
    cdm
    #
    @7
    cmpt
    @8
    vx
    cA
    cxdiv
    cM
    @0
    crp
    ofcfval3
    @3
    vx
    @9
    cS
    @7
    @1
    @9
    cS
    wceq
    #
    @2
    @1
    cS
    cc0
    cpnf
    cicc
    co
    #
    cM
    wf
    @10
    cS
    cM
    measfrge0
    cS
    @11
    cM
    fdm
    syl
    adantr
    mpteq1d
    eqtrd
    @3
    cS
    @11
    @8
    wf
    #
    c0
    @8
    cfv
    #
    cc0
    wceq
    #
    vy
    cv
    #
    com
    cdom
    wbr
    #
    vz
    @15
    vz
    cv
    #
    wdisj
    #
    wa
    #
    @15
    cuni
    #
    @8
    cfv
    #
    @15
    @17
    @8
    cfv
    #
    vz
    cesum
    #
    wceq
    #
    wi
    #
    vy
    cS
    cpw
    #
    wral
    #
    @8
    @0
    wcel
    #
    @3
    vx
    cS
    @7
    @11
    @8
    @3
    @5
    cS
    wcel
    #
    wa
    @6
    cA
    @1
    @29
    @6
    @11
    wcel
    @2
    @5
    cS
    cM
    measvxrge0
    adantlr
    @1
    @2
    @29
    simplr
    xrpxdivcld
    @8
    eqid
    #
    fmptd
    @3
    @13
    c0
    cM
    cfv
    #
    cA
    cxdiv
    co
    #
    cc0
    @3
    c0
    cS
    wcel
    #
    @32
    cvv
    wcel
    @13
    @32
    wceq
    @1
    @33
    @2
    @1
    cS
    csiga
    crn
    cuni
    wcel
    #
    @33
    cS
    cM
    measbase
    #
    cS
    0elsiga
    syl
    adantr
    @31
    cA
    cxdiv
    ovex
    vx
    c0
    @7
    @32
    cS
    cvv
    @8
    @5
    c0
    wceq
    @6
    @31
    cA
    cxdiv
    @5
    c0
    cM
    fveq2
    oveq1d
    @30
    fvmptg
    sylancl
    @1
    @2
    @32
    cc0
    cA
    cxdiv
    co
    cc0
    @1
    @31
    cc0
    cA
    cxdiv
    cS
    cM
    measvnul
    oveq1d
    cA
    xdiv0rp
    sylan9eq
    eqtrd
    @3
    @25
    vy
    @26
    @3
    @15
    @26
    wcel
    #
    wa
    #
    @19
    @24
    @37
    @19
    wa
    @3
    @36
    @16
    @18
    @24
    @3
    @36
    @19
    simpll
    @3
    @36
    @19
    simplr
    @37
    @16
    @18
    simprl
    @37
    @16
    @18
    simprr
    @3
    @36
    @16
    @18
    w3a
    #
    wa
    #
    @15
    @17
    cM
    cfv
    #
    vz
    cesum
    #
    cA
    cxdiv
    co
    #
    @15
    @40
    cA
    cxdiv
    co
    #
    vz
    cesum
    #
    @21
    @23
    @3
    @16
    @36
    @42
    @44
    wceq
    @18
    @37
    @15
    @40
    cA
    vz
    cvv
    @15
    cvv
    wcel
    @37
    vy
    vex
    a1i
    @37
    @17
    @15
    wcel
    #
    wa
    @1
    @17
    cS
    wcel
    #
    @40
    @11
    wcel
    @1
    @2
    @36
    @45
    simplll
    @36
    @45
    @46
    @3
    @36
    @15
    cS
    wss
    @45
    @46
    vy
    cS
    selpw
    @15
    cS
    @17
    ssel2
    sylanb
    #
    adantll
    @17
    cS
    cM
    measvxrge0
    syl2anc
    @1
    @2
    @36
    simplr
    esumdivc
    3ad2antr1
    @39
    @21
    @20
    cM
    cfv
    #
    cA
    cxdiv
    co
    #
    @42
    @39
    @20
    cS
    wcel
    #
    @21
    @49
    wceq
    @39
    @34
    @36
    @16
    @50
    @1
    @34
    @2
    @38
    @35
    ad2antrr
    @3
    @36
    @16
    @18
    simpr1
    #
    @3
    @36
    @16
    @18
    simpr2
    #
    @15
    cS
    sigaclcu
    syl3anc
    vx
    @20
    @7
    @49
    cS
    @8
    @5
    @20
    wceq
    @6
    @48
    cA
    cxdiv
    @5
    @20
    cM
    fveq2
    oveq1d
    @30
    @6
    cA
    cxdiv
    ovex
    #
    fvmpt3i
    syl
    @39
    @48
    @41
    cA
    cxdiv
    @39
    @1
    @36
    @16
    @18
    @48
    @41
    wceq
    @1
    @2
    @38
    simpll
    @51
    @52
    @3
    @36
    @16
    @18
    simpr3
    vz
    @15
    cS
    cM
    measvun
    syl112anc
    oveq1d
    eqtrd
    @39
    @36
    @23
    @44
    wceq
    @51
    @36
    @15
    @22
    @43
    vz
    @36
    @45
    wa
    @46
    @22
    @43
    wceq
    @47
    vx
    @17
    @7
    @43
    cS
    @8
    @5
    @17
    wceq
    @6
    @40
    cA
    cxdiv
    @5
    @17
    cM
    fveq2
    oveq1d
    @30
    @53
    fvmpt3i
    syl
    esumeq2dv
    syl
    3eqtr4d
    syl13anc
    ex
    ralrimiva
    @1
    @12
    @14
    @27
    w3a
    #
    @28
    wi
    @2
    @1
    @28
    @54
    @1
    @34
    @28
    @54
    wb
    @35
    vy
    vz
    cS
    @8
    ismeas
    syl
    biimprd
    adantr
    mp3and
    eqeltrd
end
