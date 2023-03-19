include "wf1.mm"
include "wss.mm"
include "wo.mm"
include "wral.mm"
include "wa.mm"
include "ciun.mm"
include "wf.mm"
include "ccnv.mm"
include "wfun.mm"
include "wfn.mm"
include "crn.mm"
include "cdm.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "cab.mm"
include "cuni.mm"
include "wcel.mm"
include "vex.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab.mm"
include "r19.29.mm"
include "nfv.mm"
include "nfre1.mm"
include "nfab.mm"
include "nfral.mm"
include "nfan.mm"
include "wi.mm"
include "f1eq1.mm"
include "biimparc.mm"
include "df-f1.mm"
include "ffun.mm"
include "anim1i.mm"
include "sylbi.mm"
include "syl.mm"
include "adantlr.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "wb.mm"
include "sseq12.mm"
include "ancoms.mm"
include "orbi12d.mm"
include "biimprcd.mm"
include "expdimp.mm"
include "rexlimivw.mm"
include "imp.mm"
include "sylan.mm"
include "an32s.mm"
include "adantlll.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "jca.mm"
include "a1i.mm"
include "rexlimi.mm"
include "fun11uni.mm"
include "simpld.mm"
include "dfiun2.mm"
include "funeqi.mm"
include "sylibr.mm"
include "cop.mm"
include "wex.mm"
include "nfra1.mm"
include "rsp.mm"
include "eldm2.mm"
include "f1dm.mm"
include "eleq2d.mm"
include "syl5bbr.mm"
include "adantr.mm"
include "syl6.mm"
include "rexbida.mm"
include "eliun.mm"
include "exbii.mm"
include "rexcom4.mm"
include "3bitr4i.mm"
include "3bitr4g.mm"
include "eqrdv.mm"
include "df-fn.mm"
include "sylanbrc.mm"
include "rniun.mm"
include "f1f.mm"
include "frn.mm"
include "ralimi.mm"
include "iunss.mm"
include "syl5eqss.mm"
include "df-f.mm"
include "simprd.mm"
include "cnveqi.mm"

theorem fun11iun
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  assume fun11iun.1: |- ( x = y -> B = C )
  assume fun11iun.2: |- B e. _V

  disjoint A x
  disjoint A y
  disjoint B y
  disjoint C x
  disjoint S x
  disjoint A u
  disjoint A v
  disjoint A z
  disjoint u v
  disjoint u x
  disjoint u z
  disjoint v x
  disjoint v z
  disjoint x z
  disjoint u y
  disjoint v y
  disjoint B u
  disjoint B v
  disjoint B z
  disjoint C u
  disjoint C v
  disjoint D u
  disjoint D v
  disjoint S u
  disjoint S v
  assert |- ( A. x e. A ( B : D -1-1-> S /\ A. y e. A ( B C_ C \/ C C_ B ) ) -> U_ x e. A B : U_ x e. A D -1-1-> S )

  proof
    cD
    cS
    cB
    wf1
    #
    cB
    cC
    wss
    #
    cC
    cB
    wss
    #
    wo
    #
    vy
    cA
    wral
    #
    wa
    #
    vx
    cA
    wral
    #
    vx
    cA
    cD
    ciun
    #
    cS
    vx
    cA
    cB
    ciun
    #
    wf
    #
    @8
    ccnv
    #
    wfun
    #
    @7
    cS
    @8
    wf1
    @6
    @8
    @7
    wfn
    #
    @8
    crn
    #
    cS
    wss
    @9
    @6
    @8
    wfun
    #
    @8
    cdm
    #
    @7
    wceq
    @12
    @6
    vz
    cv
    #
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    vz
    cab
    #
    cuni
    #
    wfun
    #
    @14
    @6
    @21
    @20
    ccnv
    #
    wfun
    #
    @6
    vu
    cv
    #
    wfun
    #
    @24
    ccnv
    wfun
    #
    wa
    #
    @24
    vv
    cv
    #
    wss
    #
    @28
    @24
    wss
    #
    wo
    #
    vv
    @19
    wral
    #
    wa
    #
    vu
    @19
    wral
    @21
    @23
    wa
    @6
    @33
    vu
    @19
    @24
    @19
    wcel
    @6
    @24
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    @33
    @18
    @35
    vz
    @24
    vu
    vex
    #
    @16
    @24
    wceq
    @17
    @34
    vx
    cA
    @16
    @24
    cB
    eqeq1
    rexbidv
    elab
    @6
    @35
    wa
    @5
    @34
    wa
    #
    vx
    cA
    wrex
    @33
    @5
    @34
    vx
    cA
    r19.29
    @37
    @33
    vx
    cA
    @27
    @32
    vx
    @27
    vx
    nfv
    @31
    vx
    vv
    @19
    @18
    vx
    vz
    @17
    vx
    cA
    nfre1
    nfab
    @31
    vx
    nfv
    nfral
    nfan
    @37
    @33
    wi
    vx
    cv
    #
    cA
    wcel
    #
    @37
    @27
    @32
    @0
    @34
    @27
    @4
    @0
    @34
    wa
    cD
    cS
    @24
    wf1
    #
    @27
    @34
    @40
    @0
    cD
    cS
    @24
    cB
    f1eq1
    biimparc
    @40
    cD
    cS
    @24
    wf
    #
    @26
    wa
    @27
    cD
    cS
    @24
    df-f1
    @41
    @25
    @26
    cD
    cS
    @24
    ffun
    anim1i
    sylbi
    syl
    adantlr
    @37
    @31
    vv
    @19
    @28
    @19
    wcel
    @37
    @28
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    @31
    @18
    @43
    vz
    @28
    vv
    vex
    @16
    @28
    wceq
    @17
    @42
    vx
    cA
    @16
    @28
    cB
    eqeq1
    rexbidv
    elab
    @43
    @37
    @28
    cC
    wceq
    #
    vy
    cA
    wrex
    #
    @31
    @42
    @44
    vx
    vy
    cA
    @38
    vy
    cv
    wceq
    cB
    cC
    @28
    fun11iun.1
    eqeq2d
    cbvrexv
    @4
    @34
    @45
    @31
    @0
    @4
    @45
    @34
    @31
    @4
    @45
    wa
    @3
    @44
    wa
    #
    vy
    cA
    wrex
    #
    @34
    @31
    @3
    @44
    vy
    cA
    r19.29
    @47
    @34
    @31
    @46
    @34
    @31
    wi
    vy
    cA
    @3
    @44
    @34
    @31
    @44
    @34
    wa
    #
    @31
    @3
    @48
    @29
    @1
    @30
    @2
    @34
    @44
    @29
    @1
    wb
    @24
    cB
    @28
    cC
    sseq12
    ancoms
    @28
    cC
    @24
    cB
    sseq12
    orbi12d
    biimprcd
    expdimp
    rexlimivw
    imp
    sylan
    an32s
    adantlll
    sylan2b
    sylan2b
    ralrimiva
    jca
    a1i
    rexlimi
    syl
    sylan2b
    ralrimiva
    @19
    vu
    vv
    fun11uni
    syl
    #
    simpld
    @8
    @20
    vx
    vz
    cA
    cB
    fun11iun.2
    dfiun2
    #
    funeqi
    sylibr
    @6
    vu
    @15
    @7
    @6
    @24
    @28
    cop
    #
    cB
    wcel
    #
    vv
    wex
    #
    vx
    cA
    wrex
    #
    @24
    cD
    wcel
    #
    vx
    cA
    wrex
    @24
    @15
    wcel
    #
    @24
    @7
    wcel
    @6
    @53
    @55
    vx
    cA
    @5
    vx
    cA
    nfra1
    @6
    @39
    @53
    @55
    wb
    #
    @6
    @39
    @5
    @57
    @5
    vx
    cA
    rsp
    @0
    @57
    @4
    @53
    @24
    cB
    cdm
    #
    wcel
    @0
    @55
    vv
    @24
    cB
    @36
    eldm2
    @0
    @58
    cD
    @24
    cD
    cS
    cB
    f1dm
    eleq2d
    syl5bbr
    adantr
    syl6
    imp
    rexbida
    @51
    @8
    wcel
    #
    vv
    wex
    @52
    vx
    cA
    wrex
    #
    vv
    wex
    @56
    @54
    @59
    @60
    vv
    vx
    @51
    cA
    cB
    eliun
    exbii
    vv
    @24
    @8
    @36
    eldm2
    @52
    vx
    vv
    cA
    rexcom4
    3bitr4i
    vx
    @24
    cA
    cD
    eliun
    3bitr4g
    eqrdv
    @8
    @7
    df-fn
    sylanbrc
    @6
    @13
    vx
    cA
    cB
    crn
    #
    ciun
    #
    cS
    vx
    cA
    cB
    rniun
    @6
    @61
    cS
    wss
    #
    vx
    cA
    wral
    @62
    cS
    wss
    @5
    @63
    vx
    cA
    @0
    @63
    @4
    @0
    cD
    cS
    cB
    wf
    @63
    cD
    cS
    cB
    f1f
    cD
    cS
    cB
    frn
    syl
    adantr
    ralimi
    vx
    cA
    @61
    cS
    iunss
    sylibr
    syl5eqss
    @7
    cS
    @8
    df-f
    sylanbrc
    @6
    @23
    @11
    @6
    @21
    @23
    @49
    simprd
    @10
    @22
    @8
    @20
    @50
    cnveqi
    funeqi
    sylibr
    @7
    cS
    @8
    df-f1
    sylanbrc
end
