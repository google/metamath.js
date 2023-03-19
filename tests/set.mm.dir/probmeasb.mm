include "cmeas.mm"
include "cfv.mm"
include "wcel.mm"
include "crp.mm"
include "w3a.mm"
include "cv.mm"
include "cin.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "cuni.mm"
include "cdm.mm"
include "c1.mm"
include "wceq.mm"
include "cprb.mm"
include "cxdiv.mm"
include "measinb.mm"
include "measdivcstOLD.mm"
include "stoic3.mm"
include "wa.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "eqidd.mm"
include "simpr.mm"
include "ineq1d.mm"
include "fveq2d.mm"
include "simp1.mm"
include "adantr.mm"
include "csiga.mm"
include "measbase.mm"
include "syl.mm"
include "simp2.mm"
include "inelsiga.mm"
include "syl3anc.mm"
include "measvxrge0.mm"
include "syl2anc.mm"
include "fvmptd.mm"
include "oveq1d.mm"
include "cr.mm"
include "wne.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "iccssxr.mm"
include "sseldi.mm"
include "simp3.mm"
include "rpred.mm"
include "0xr.mm"
include "pnfxr.mm"
include "iccgelb.mm"
include "mp3an12.mm"
include "wss.mm"
include "inss2.mm"
include "a1i.mm"
include "measssd.mm"
include "xrrege0.mm"
include "syl22anc.mm"
include "rpne0d.mm"
include "rexdiv.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "wral.mm"
include "rerpdivcld.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "eqcomd.mm"
include "3eltr3d.mm"
include "measbasedom.mm"
include "sylibr.mm"
include "unieqd.mm"
include "rpcnd.mm"
include "incom.mm"
include "elssuni.mm"
include "df-ss.mm"
include "sylib.mm"
include "syl5eq.mm"
include "diveq1bd.mm"
include "sgon.mm"
include "baselsiga.mm"
include "4syl.mm"
include "1red.mm"
include "elprob.mm"
include "sylanbrc.mm"

theorem probmeasb
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cM: class M
  let vy: setvar y

  disjoint A x
  disjoint M x
  disjoint S x
  disjoint x y
  disjoint A y
  disjoint M y
  disjoint S y
  assert |- ( ( M e. ( measures ` S ) /\ A e. S /\ ( M ` A ) e. RR+ ) -> ( x e. S |-> ( ( M ` ( x i^i A ) ) / ( M ` A ) ) ) e. Prob )

  proof
    cM
    cS
    cmeas
    cfv
    #
    wcel
    #
    cA
    cS
    wcel
    #
    cA
    cM
    cfv
    #
    crp
    wcel
    #
    w3a
    #
    vx
    cS
    vx
    cv
    #
    cA
    cin
    #
    cM
    cfv
    #
    @3
    cdiv
    co
    #
    cmpt
    #
    cmeas
    crn
    cuni
    wcel
    #
    @10
    cdm
    #
    cuni
    #
    @10
    cfv
    #
    c1
    wceq
    @10
    cprb
    wcel
    @5
    @10
    @12
    cmeas
    cfv
    #
    wcel
    @11
    @5
    vx
    cS
    @6
    vy
    cS
    vy
    cv
    #
    cA
    cin
    #
    cM
    cfv
    #
    cmpt
    #
    cfv
    #
    @3
    cxdiv
    co
    #
    cmpt
    #
    @0
    @10
    @15
    @1
    @2
    @19
    @0
    wcel
    @4
    @22
    @0
    wcel
    vy
    cA
    cS
    cM
    measinb
    vx
    @3
    cS
    @19
    measdivcstOLD
    stoic3
    @5
    vx
    cS
    @21
    @9
    @5
    @6
    cS
    wcel
    #
    wa
    #
    @21
    @8
    @3
    cxdiv
    co
    #
    @9
    @24
    @20
    @8
    @3
    cxdiv
    @24
    vy
    @6
    @18
    @8
    cS
    @19
    cc0
    cpnf
    cicc
    co
    #
    @24
    @19
    eqidd
    @24
    @16
    @6
    wceq
    #
    wa
    #
    @17
    @7
    cM
    @28
    @16
    @6
    cA
    @24
    @27
    simpr
    ineq1d
    fveq2d
    @5
    @23
    simpr
    #
    @24
    @1
    @7
    cS
    wcel
    #
    @8
    @26
    wcel
    #
    @5
    @1
    @23
    @1
    @2
    @4
    simp1
    #
    adantr
    #
    @24
    cS
    csiga
    crn
    cuni
    wcel
    #
    @23
    @2
    @30
    @24
    @1
    @34
    @33
    cS
    cM
    measbase
    #
    syl
    @29
    @5
    @2
    @23
    @1
    @2
    @4
    simp2
    #
    adantr
    #
    @6
    cA
    cS
    inelsiga
    syl3anc
    #
    @7
    cS
    cM
    measvxrge0
    syl2anc
    #
    fvmptd
    oveq1d
    @24
    @8
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    @3
    cc0
    wne
    #
    @25
    @9
    wceq
    @24
    @8
    cxr
    wcel
    @41
    cc0
    @8
    cle
    wbr
    #
    @8
    @3
    cle
    wbr
    @40
    @24
    @26
    cxr
    @8
    cc0
    cpnf
    iccssxr
    @39
    sseldi
    @24
    @3
    @5
    @4
    @23
    @1
    @2
    @4
    simp3
    #
    adantr
    #
    rpred
    #
    @24
    @31
    @43
    @39
    cc0
    cxr
    wcel
    cpnf
    cxr
    wcel
    @31
    @43
    0xr
    pnfxr
    cc0
    cpnf
    @8
    iccgelb
    mp3an12
    syl
    @24
    @7
    cA
    cS
    cM
    @33
    @38
    @37
    @7
    cA
    wss
    @24
    @6
    cA
    inss2
    a1i
    measssd
    @8
    @3
    xrrege0
    syl22anc
    #
    @46
    @24
    @3
    @45
    rpne0d
    @8
    @3
    rexdiv
    syl3anc
    eqtrd
    mpteq2dva
    @5
    @15
    @0
    @5
    @12
    cS
    cmeas
    @5
    @9
    cr
    wcel
    #
    vx
    cS
    wral
    @12
    cS
    wceq
    @5
    @48
    vx
    cS
    @24
    @8
    @3
    @47
    @45
    rerpdivcld
    ralrimiva
    vx
    cS
    @9
    cr
    dmmptg
    syl
    #
    fveq2d
    eqcomd
    3eltr3d
    @10
    measbasedom
    sylibr
    @5
    @14
    cS
    cuni
    #
    @10
    cfv
    c1
    @5
    @13
    @50
    @10
    @5
    @12
    cS
    @49
    unieqd
    fveq2d
    @5
    vx
    @50
    @9
    c1
    cS
    @10
    cr
    @5
    @10
    eqidd
    @5
    @6
    @50
    wceq
    #
    wa
    #
    @8
    @3
    @52
    @3
    @5
    @4
    @51
    @44
    adantr
    rpcnd
    @5
    @42
    @51
    @5
    @3
    @44
    rpne0d
    adantr
    @52
    @7
    cA
    cM
    @52
    @7
    @50
    cA
    cin
    #
    cA
    @52
    @6
    @50
    cA
    @5
    @51
    simpr
    ineq1d
    @5
    @53
    cA
    wceq
    #
    @51
    @5
    @2
    @54
    @36
    @2
    @53
    cA
    @50
    cin
    #
    cA
    @50
    cA
    incom
    @2
    cA
    @50
    wss
    @55
    cA
    wceq
    cA
    cS
    elssuni
    cA
    @50
    df-ss
    sylib
    syl5eq
    syl
    adantr
    eqtrd
    fveq2d
    diveq1bd
    @5
    @1
    @34
    cS
    @50
    csiga
    cfv
    wcel
    @50
    cS
    wcel
    @32
    @35
    cS
    sgon
    @50
    cS
    baselsiga
    4syl
    @5
    1red
    fvmptd
    eqtrd
    @10
    elprob
    sylanbrc
end
