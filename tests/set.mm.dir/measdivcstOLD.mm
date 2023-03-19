include "cmeas.mm"
include "cfv.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "cxdiv.mm"
include "cmpt.mm"
include "wf.mm"
include "c0.mm"
include "wceq.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "cuni.mm"
include "cesum.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "w3a.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wfun.mm"
include "cdm.mm"
include "funmpt.mm"
include "cvv.mm"
include "ovex.mm"
include "rgenw.mm"
include "dmmptg.mm"
include "ax-mp.mm"
include "df-fn.mm"
include "mpbir2an.mm"
include "a1i.mm"
include "wrex.mm"
include "wb.mm"
include "vex.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "measfrge0.mm"
include "ffvelrn.mm"
include "sylan.mm"
include "adantlr.mm"
include "simplr.mm"
include "xrpxdivcld.mm"
include "eleq1a.mm"
include "syl.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "csiga.mm"
include "measbase.mm"
include "0elsiga.mm"
include "adantr.mm"
include "jctir.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "fvmptg.mm"
include "measvnul.mm"
include "xdiv0rp.mm"
include "sylan9eq.mm"
include "eqtrd.mm"
include "simpll.mm"
include "simprl.mm"
include "simprr.mm"
include "3jca.mm"
include "simplll.mm"
include "simpr.mm"
include "elpwg.mm"
include "ssel2.mm"
include "sylanb.mm"
include "syl2anc.mm"
include "measvxrge0.mm"
include "esumdivc.mm"
include "3ad2antr1.mm"
include "ad2antrr.mm"
include "simpr1.mm"
include "simpr2.mm"
include "sigaclcu.mm"
include "syl3anc.mm"
include "fvmpt3i.mm"
include "jca.mm"
include "simpr3.mm"
include "measvun.mm"
include "3expia.mm"
include "ralrimiva.mm"
include "r19.21bi.mm"
include "sylc.mm"
include "esumeq2dv.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "ismeas.mm"
include "biimprd.mm"
include "mpd.mm"

theorem measdivcstOLD
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cM: class M
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint M x
  disjoint S x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint M y
  disjoint M z
  disjoint S y
  disjoint S z
  assert |- ( ( M e. ( measures ` S ) /\ A e. RR+ ) -> ( x e. S |-> ( ( M ` x ) /e A ) ) e. ( measures ` S ) )

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
    cS
    cc0
    cpnf
    cicc
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
    @12
    vz
    cv
    #
    wdisj
    #
    wa
    #
    @12
    cuni
    #
    @8
    cfv
    #
    @12
    @14
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
    w3a
    #
    @8
    @0
    wcel
    #
    @3
    @9
    @11
    @24
    @3
    @8
    cS
    wfn
    #
    @8
    crn
    #
    @4
    wss
    @9
    @27
    @3
    @27
    @8
    wfun
    @8
    cdm
    cS
    wceq
    #
    vx
    cS
    @7
    funmpt
    @7
    cvv
    wcel
    #
    vx
    cS
    wral
    @29
    @30
    vx
    cS
    @6
    cA
    cxdiv
    ovex
    #
    rgenw
    vx
    cS
    @7
    cvv
    dmmptg
    ax-mp
    @8
    cS
    df-fn
    mpbir2an
    a1i
    @3
    vy
    @28
    @4
    @12
    @28
    wcel
    #
    @12
    @7
    wceq
    #
    vx
    cS
    wrex
    #
    @3
    @12
    @4
    wcel
    #
    @12
    cvv
    wcel
    #
    @32
    @34
    wb
    vy
    vex
    #
    vx
    cS
    @7
    @12
    @8
    cvv
    @8
    eqid
    #
    elrnmpt
    ax-mp
    @3
    @33
    @35
    vx
    cS
    @3
    @5
    cS
    wcel
    #
    wa
    #
    @7
    @4
    wcel
    @33
    @35
    wi
    @40
    @6
    cA
    @1
    @39
    @6
    @4
    wcel
    #
    @2
    @1
    cS
    @4
    cM
    wf
    @39
    @41
    cS
    cM
    measfrge0
    cS
    @4
    @5
    cM
    ffvelrn
    sylan
    adantlr
    @1
    @2
    @39
    simplr
    xrpxdivcld
    @7
    @4
    @12
    eleq1a
    syl
    rexlimdva
    syl5bi
    ssrdv
    cS
    @4
    @8
    df-f
    sylanbrc
    @3
    @10
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
    @43
    cvv
    wcel
    #
    wa
    @10
    @43
    wceq
    @3
    @44
    @45
    @1
    @44
    @2
    @1
    cS
    csiga
    crn
    cuni
    wcel
    #
    @44
    cS
    cM
    measbase
    #
    cS
    0elsiga
    syl
    adantr
    @42
    cA
    cxdiv
    ovex
    jctir
    vx
    c0
    @7
    @43
    cS
    cvv
    @8
    @5
    c0
    wceq
    @6
    @42
    cA
    cxdiv
    @5
    c0
    cM
    fveq2
    oveq1d
    @38
    fvmptg
    syl
    @1
    @2
    @43
    cc0
    cA
    cxdiv
    co
    cc0
    @1
    @42
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
    @22
    vy
    @23
    @3
    @12
    @23
    wcel
    #
    wa
    #
    @16
    @21
    @49
    @16
    wa
    #
    @3
    @48
    @13
    @15
    w3a
    #
    @21
    @3
    @48
    @16
    simpll
    @50
    @48
    @13
    @15
    @3
    @48
    @16
    simplr
    @49
    @13
    @15
    simprl
    @49
    @13
    @15
    simprr
    3jca
    @3
    @51
    wa
    #
    @12
    @14
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
    @12
    @53
    cA
    cxdiv
    co
    #
    vz
    cesum
    #
    @18
    @20
    @3
    @13
    @48
    @55
    @57
    wceq
    @15
    @49
    @12
    @53
    cA
    vz
    cvv
    @36
    @49
    @37
    a1i
    @49
    @14
    @12
    wcel
    #
    wa
    #
    @1
    @14
    cS
    wcel
    #
    @53
    @4
    wcel
    @1
    @2
    @48
    @58
    simplll
    @59
    @48
    @58
    @60
    @3
    @48
    @58
    simplr
    @49
    @58
    simpr
    @48
    @12
    cS
    wss
    #
    @58
    @60
    @36
    @48
    @61
    wb
    @37
    @12
    cS
    cvv
    elpwg
    ax-mp
    @12
    cS
    @14
    ssel2
    sylanb
    #
    syl2anc
    @14
    cS
    cM
    measvxrge0
    syl2anc
    @1
    @2
    @48
    simplr
    esumdivc
    3ad2antr1
    @52
    @18
    @17
    cM
    cfv
    #
    cA
    cxdiv
    co
    #
    @55
    @52
    @17
    cS
    wcel
    #
    @18
    @64
    wceq
    @52
    @46
    @48
    @13
    @65
    @1
    @46
    @2
    @51
    @47
    ad2antrr
    @3
    @48
    @13
    @15
    simpr1
    #
    @3
    @48
    @13
    @15
    simpr2
    #
    @12
    cS
    sigaclcu
    syl3anc
    vx
    @17
    @7
    @64
    cS
    @8
    @5
    @17
    wceq
    @6
    @63
    cA
    cxdiv
    @5
    @17
    cM
    fveq2
    oveq1d
    @38
    @31
    fvmpt3i
    syl
    @52
    @63
    @54
    cA
    cxdiv
    @52
    @1
    @48
    wa
    @16
    @63
    @54
    wceq
    #
    @52
    @1
    @48
    @1
    @2
    @51
    simpll
    @66
    jca
    @52
    @13
    @15
    @67
    @3
    @48
    @13
    @15
    simpr3
    jca
    @1
    @16
    @68
    wi
    #
    vy
    @23
    @1
    @69
    vy
    @23
    @1
    @48
    @16
    @68
    vz
    @12
    cS
    cM
    measvun
    3expia
    ralrimiva
    r19.21bi
    sylc
    oveq1d
    eqtrd
    @52
    @48
    @20
    @57
    wceq
    @66
    @48
    @12
    @19
    @56
    vz
    @48
    @58
    wa
    @60
    @19
    @56
    wceq
    @62
    vx
    @14
    @7
    @56
    cS
    @8
    @5
    @14
    wceq
    @6
    @53
    cA
    cxdiv
    @5
    @14
    cM
    fveq2
    oveq1d
    @38
    @31
    fvmpt3i
    syl
    esumeq2dv
    syl
    3eqtr4d
    syl2anc
    ex
    ralrimiva
    3jca
    @1
    @25
    @26
    wi
    @2
    @1
    @26
    @25
    @1
    @46
    @26
    @25
    wb
    @47
    vy
    vz
    cS
    @8
    ismeas
    syl
    biimprd
    adantr
    mpd
end
