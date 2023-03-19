include "wcel.mm"
include "con0.mm"
include "cpw.mm"
include "cdm.mm"
include "wa.mm"
include "wral.mm"
include "w3a.mm"
include "ciun.mm"
include "wss.mm"
include "cxp.mm"
include "cwdom.mm"
include "wbr.mm"
include "char.mm"
include "cfv.mm"
include "elpwi.mm"
include "adantr.mm"
include "ralimi.mm"
include "iunss.mm"
include "sylibr.mm"
include "3ad2ant3.mm"
include "cvv.mm"
include "cv.mm"
include "c2nd.mm"
include "c1st.mm"
include "csb.mm"
include "cep.mm"
include "coi.mm"
include "xpexg.mm"
include "3adant3.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "rsp.mm"
include "onelss.mm"
include "imp.mm"
include "adantrl.mm"
include "wfo.mm"
include "wf.mm"
include "crn.mm"
include "wsmo.mm"
include "oismo.mm"
include "syl.mm"
include "ad2antrl.mm"
include "simprd.mm"
include "oif.mm"
include "jctil.mm"
include "dffo2.mm"
include "dffo3.mm"
include "simprbi.mm"
include "3syl.mm"
include "3impia.mm"
include "ssrexv.mm"
include "sylc.mm"
include "3exp.mm"
include "sylan9r.mm"
include "reximdai.mm"
include "3adant1.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfoi.mm"
include "nffv.mm"
include "nfeq2.mm"
include "nfrex.mm"
include "csbeq1a.mm"
include "oieq2.mm"
include "syl5eq.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "cbvrex.mm"
include "syl6ib.mm"
include "eliun.mm"
include "cop.mm"
include "vex.mm"
include "op1std.mm"
include "csbeq1d.mm"
include "op2ndd.mm"
include "fveq12d.mm"
include "rexxp.mm"
include "3imtr4g.mm"
include "wdomd.mm"
include "hsmexlem1.mm"
include "syl2anc.mm"

theorem hsmexlem2
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  assume hsmexlem.f: |- F = OrdIso ( _E , B )
  assume hsmexlem.g: |- G = OrdIso ( _E , U_ a e. A B )

  disjoint A a
  disjoint C a
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint A b
  disjoint c d
  disjoint c e
  disjoint A c
  disjoint d e
  disjoint A d
  disjoint A e
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B e
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint C e
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F e
  disjoint V b
  disjoint V c
  assert |- ( ( A e. V /\ C e. On /\ A. a e. A ( B e. ~P On /\ dom F e. C ) ) -> dom G e. ( har ` ~P ( A X. C ) ) )

  proof
    cA
    cV
    wcel
    #
    cC
    con0
    wcel
    #
    cB
    con0
    cpw
    wcel
    #
    cF
    cdm
    #
    cC
    wcel
    #
    wa
    #
    va
    cA
    wral
    #
    w3a
    #
    va
    cA
    cB
    ciun
    #
    con0
    wss
    #
    @8
    cA
    cC
    cxp
    #
    cwdom
    wbr
    cG
    cdm
    @10
    cpw
    char
    cfv
    wcel
    @6
    @0
    @9
    @1
    @6
    cB
    con0
    wss
    #
    va
    cA
    wral
    @9
    @5
    @11
    va
    cA
    @2
    @11
    @4
    cB
    con0
    elpwi
    #
    adantr
    ralimi
    va
    cA
    cB
    con0
    iunss
    sylibr
    3ad2ant3
    @7
    vb
    vc
    @8
    @10
    cvv
    vc
    cv
    #
    c2nd
    cfv
    #
    va
    @13
    c1st
    cfv
    #
    cB
    csb
    #
    cep
    coi
    #
    cfv
    #
    @0
    @1
    @10
    cvv
    wcel
    @6
    cA
    cC
    cV
    con0
    xpexg
    3adant3
    @7
    vb
    cv
    #
    @8
    wcel
    #
    @19
    @18
    wceq
    #
    vc
    @10
    wrex
    #
    @7
    @19
    cB
    wcel
    #
    va
    cA
    wrex
    #
    @19
    ve
    cv
    #
    va
    vd
    cv
    #
    cB
    csb
    #
    cep
    coi
    #
    cfv
    #
    wceq
    #
    ve
    cC
    wrex
    #
    vd
    cA
    wrex
    #
    @20
    @22
    @7
    @24
    @19
    @25
    cF
    cfv
    #
    wceq
    #
    ve
    cC
    wrex
    #
    va
    cA
    wrex
    #
    @32
    @1
    @6
    @24
    @36
    wi
    @0
    @1
    @6
    wa
    @23
    @35
    va
    cA
    @1
    @6
    va
    @1
    va
    nfv
    @5
    va
    cA
    nfra1
    nfan
    @6
    va
    cv
    #
    cA
    wcel
    @5
    @1
    @23
    @35
    wi
    @5
    va
    cA
    rsp
    @1
    @5
    @23
    @35
    @1
    @5
    @23
    w3a
    @3
    cC
    wss
    #
    @34
    ve
    @3
    wrex
    #
    @35
    @1
    @5
    @38
    @23
    @1
    @4
    @38
    @2
    @1
    @4
    @38
    cC
    @3
    onelss
    imp
    adantrl
    3adant3
    @1
    @5
    @23
    @39
    @1
    @5
    wa
    #
    @3
    cB
    cF
    wfo
    #
    @39
    vb
    cB
    wral
    #
    @23
    @39
    wi
    @40
    @3
    cB
    cF
    wf
    #
    cF
    crn
    cB
    wceq
    #
    wa
    @41
    @40
    @44
    @43
    @40
    cF
    wsmo
    #
    @44
    @2
    @45
    @44
    wa
    #
    @1
    @4
    @2
    @11
    @46
    @12
    cB
    cF
    hsmexlem.f
    oismo
    syl
    ad2antrl
    simprd
    cB
    cep
    cF
    hsmexlem.f
    oif
    jctil
    @3
    cB
    cF
    dffo2
    sylibr
    @41
    @43
    @42
    ve
    vb
    @3
    cB
    cF
    dffo3
    simprbi
    @39
    vb
    cB
    rsp
    3syl
    3impia
    @34
    ve
    @3
    cC
    ssrexv
    sylc
    3exp
    sylan9r
    reximdai
    3adant1
    @35
    @31
    va
    vd
    cA
    @35
    vd
    nfv
    @30
    va
    ve
    cC
    va
    cC
    nfcv
    va
    @19
    @29
    va
    @25
    @28
    va
    @27
    cep
    va
    cep
    nfcv
    va
    @26
    cB
    nfcsb1v
    nfoi
    va
    @25
    nfcv
    nffv
    nfeq2
    nfrex
    @37
    @26
    wceq
    #
    @34
    @30
    ve
    cC
    @47
    @33
    @29
    @19
    @47
    @25
    cF
    @28
    @47
    cF
    cB
    cep
    coi
    #
    @28
    hsmexlem.f
    @47
    cB
    @27
    wceq
    @48
    @28
    wceq
    va
    @26
    cB
    csbeq1a
    cB
    @27
    cep
    oieq2
    syl
    syl5eq
    fveq1d
    eqeq2d
    rexbidv
    cbvrex
    syl6ib
    va
    @19
    cA
    cB
    eliun
    @21
    @30
    vc
    vd
    ve
    cA
    cC
    @13
    @26
    @25
    cop
    wceq
    #
    @18
    @29
    @19
    @49
    @14
    @25
    @17
    @28
    @49
    @16
    @27
    wceq
    @17
    @28
    wceq
    @49
    va
    @15
    @26
    cB
    @26
    @25
    @13
    vd
    vex
    #
    ve
    vex
    #
    op1std
    csbeq1d
    @16
    @27
    cep
    oieq2
    syl
    @26
    @25
    @13
    @50
    @51
    op2ndd
    fveq12d
    eqeq2d
    rexxp
    3imtr4g
    imp
    wdomd
    @8
    @10
    cG
    hsmexlem.g
    hsmexlem1
    syl2anc
end
