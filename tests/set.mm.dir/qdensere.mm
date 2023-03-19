include "cq.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "ccl.mm"
include "cr.mm"
include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "retop.mm"
include "qssre.mm"
include "uniretop.mm"
include "clsss3.mm"
include "mp2an.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "co.mm"
include "wceq.mm"
include "cxr.mm"
include "wrex.mm"
include "cxp.mm"
include "cpw.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "ioof.mm"
include "ffn.mm"
include "ovelrn.mm"
include "mp2b.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "elioo3g.mm"
include "simplbi.mm"
include "simp1d.mm"
include "ad2antrr.mm"
include "simp2d.mm"
include "qre.mm"
include "ad2antlr.mm"
include "rexrd.mm"
include "3jca.mm"
include "simpr.mm"
include "sylanbrc.mm"
include "simplr.mm"
include "inelcm.mm"
include "syl2anc.mm"
include "simp3d.mm"
include "eliooord.mm"
include "simpld.mm"
include "simprd.mm"
include "xrlttrd.mm"
include "qbtwnxr.mm"
include "syl3anc.mm"
include "r19.29a.mm"
include "a1i.mm"
include "eleq2.mm"
include "ineq1.mm"
include "neeq1d.mm"
include "3imtr4d.mm"
include "rexlimivw.mm"
include "sylbi.mm"
include "rgen.mm"
include "eqidd.mm"
include "cuni.mm"
include "ctb.mm"
include "retopbas.mm"
include "id.mm"
include "elcls3.mm"
include "mpbiri.mm"
include "ssriv.mm"
include "eqssi.mm"

theorem qdensere
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A


  assert |- ( ( cls ` ( topGen ` ran (,) ) ) ` QQ ) = RR

  proof
    cq
    cioo
    crn
    #
    ctg
    cfv
    #
    ccl
    cfv
    cfv
    #
    cr
    @1
    ctop
    wcel
    cq
    cr
    wss
    #
    @2
    cr
    wss
    retop
    qssre
    cq
    @1
    cr
    uniretop
    clsss3
    mp2an
    vx
    cr
    @2
    vx
    cv
    #
    cr
    wcel
    #
    @4
    @2
    wcel
    @4
    vy
    cv
    #
    wcel
    #
    @6
    cq
    cin
    #
    c0
    wne
    #
    wi
    #
    vy
    @0
    wral
    @10
    vy
    @0
    @6
    @0
    wcel
    #
    @6
    vz
    cv
    #
    vw
    cv
    #
    cioo
    co
    #
    wceq
    #
    vw
    cxr
    wrex
    #
    vz
    cxr
    wrex
    #
    @10
    cxr
    cxr
    cxp
    #
    cr
    cpw
    #
    cioo
    wf
    cioo
    @18
    wfn
    @11
    @17
    wb
    ioof
    @18
    @19
    cioo
    ffn
    vz
    vw
    cxr
    cxr
    @6
    cioo
    ovelrn
    mp2b
    @16
    @10
    vz
    cxr
    @15
    @10
    vw
    cxr
    @15
    @4
    @14
    wcel
    #
    @14
    cq
    cin
    #
    c0
    wne
    #
    @7
    @9
    @20
    @22
    wi
    @15
    @20
    @12
    @6
    clt
    wbr
    @6
    @13
    clt
    wbr
    wa
    #
    @22
    vy
    cq
    @20
    @6
    cq
    wcel
    #
    wa
    #
    @23
    wa
    #
    @6
    @14
    wcel
    #
    @24
    @22
    @26
    @12
    cxr
    wcel
    #
    @13
    cxr
    wcel
    #
    @6
    cxr
    wcel
    #
    w3a
    @23
    @27
    @26
    @28
    @29
    @30
    @20
    @28
    @24
    @23
    @20
    @28
    @29
    @4
    cxr
    wcel
    #
    @20
    @28
    @29
    @31
    w3a
    @12
    @4
    clt
    wbr
    #
    @4
    @13
    clt
    wbr
    #
    wa
    @12
    @13
    @4
    elioo3g
    simplbi
    #
    simp1d
    #
    ad2antrr
    @20
    @29
    @24
    @23
    @20
    @28
    @29
    @31
    @34
    simp2d
    #
    ad2antrr
    @26
    @6
    @24
    @6
    cr
    wcel
    @20
    @23
    @6
    qre
    ad2antlr
    rexrd
    3jca
    @25
    @23
    simpr
    @12
    @13
    @6
    elioo3g
    sylanbrc
    @20
    @24
    @23
    simplr
    @6
    @14
    cq
    inelcm
    syl2anc
    @20
    @28
    @29
    @12
    @13
    clt
    wbr
    @23
    vy
    cq
    wrex
    @35
    @36
    @20
    @12
    @4
    @13
    @35
    @20
    @28
    @29
    @31
    @34
    simp3d
    @36
    @20
    @32
    @33
    @4
    @12
    @13
    eliooord
    #
    simpld
    @20
    @32
    @33
    @37
    simprd
    xrlttrd
    vy
    @12
    @13
    qbtwnxr
    syl3anc
    r19.29a
    a1i
    @6
    @14
    @4
    eleq2
    @15
    @8
    @21
    c0
    @6
    @14
    cq
    ineq1
    neeq1d
    3imtr4d
    rexlimivw
    rexlimivw
    sylbi
    rgen
    @5
    vy
    @0
    @4
    cq
    @1
    cr
    @5
    @1
    eqidd
    cr
    @1
    cuni
    wceq
    @5
    uniretop
    a1i
    @0
    ctb
    wcel
    @5
    retopbas
    a1i
    @3
    @5
    qssre
    a1i
    @5
    id
    elcls3
    mpbiri
    ssriv
    eqssi
end
