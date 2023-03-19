include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "cxp.mm"
include "cv.mm"
include "ccom.mm"
include "wceq.mm"
include "weu.mm"
include "cfv.mm"
include "cop.mm"
include "cmpt.mm"
include "cvv.mm"
include "mptexg.mm"
include "eueq.mm"
include "sylib.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "wfn.mm"
include "ffn.mm"
include "adantl.mm"
include "wral.mm"
include "ffvelrn.mm"
include "opelxpi.mm"
include "syl2an.mm"
include "anandirs.mm"
include "ralrimiva.mm"
include "3adant1.mm"
include "eqid.mm"
include "fmpt.mm"
include "syl.mm"
include "adantr.mm"
include "c1st.mm"
include "c2nd.mm"
include "xpss.mm"
include "sseldi.mm"
include "3ad2antl1.mm"
include "adantll.mm"
include "cres.mm"
include "fveq1.mm"
include "coeq1i.mm"
include "fveq1i.mm"
include "syl6eq.mm"
include "3ad2ant2.mm"
include "ad2antlr.mm"
include "simpr1.mm"
include "fvco3.mm"
include "sylan.mm"
include "fvres.mm"
include "3eqtrrd.mm"
include "3ad2ant3.mm"
include "eqopi.mm"
include "syl12anc.mm"
include "fveq2.mm"
include "opeq12d.mm"
include "opex.mm"
include "fvmpt.mm"
include "eqtr4d.mm"
include "eqfnfvd.mm"
include "ex.mm"
include "crn.mm"
include "wss.mm"
include "wfo.mm"
include "fo1st.mm"
include "fofn.mm"
include "ax-mp.mm"
include "ssv.mm"
include "fnssres.mm"
include "mp2an.mm"
include "a1i.mm"
include "frn.mm"
include "fnco.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "3adantl1.mm"
include "fvex.mm"
include "op1st.mm"
include "syl6eqr.mm"
include "fo2nd.mm"
include "op2nd.mm"
include "3jca.mm"
include "feq1.mm"
include "coeq2.mm"
include "eqeq2d.mm"
include "3anbi123d.mm"
include "syl5ibrcom.mm"
include "impbid.mm"
include "eubidv.mm"
include "mpbird.mm"

theorem upxp
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let vh: setvar h
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vz: setvar z
  assume upxp.1: |- P = ( 1st |` ( B X. C ) )
  assume upxp.2: |- Q = ( 2nd |` ( B X. C ) )

  disjoint A h
  disjoint B h
  disjoint C h
  disjoint F h
  disjoint G h
  disjoint D h
  disjoint h x
  disjoint h z
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint B x
  disjoint B z
  disjoint C x
  disjoint C z
  disjoint F x
  disjoint F z
  disjoint G x
  disjoint G z
  disjoint D z
  disjoint P z
  disjoint Q z
  assert |- ( ( A e. D /\ F : A --> B /\ G : A --> C ) -> E! h ( h : A --> ( B X. C ) /\ F = ( P o. h ) /\ G = ( Q o. h ) ) )

  proof
    cA
    cD
    wcel
    #
    cA
    cB
    cF
    wf
    #
    cA
    cC
    cG
    wf
    #
    w3a
    #
    cA
    cB
    cC
    cxp
    #
    vh
    cv
    #
    wf
    #
    cF
    cP
    @5
    ccom
    #
    wceq
    #
    cG
    cQ
    @5
    ccom
    #
    wceq
    #
    w3a
    #
    vh
    weu
    @5
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    @12
    cG
    cfv
    #
    cop
    #
    cmpt
    #
    wceq
    #
    vh
    weu
    #
    @0
    @1
    @18
    @2
    @0
    @16
    cvv
    wcel
    @18
    vx
    cA
    @15
    cD
    mptexg
    vh
    @16
    eueq
    sylib
    3ad2ant1
    @3
    @11
    @17
    vh
    @3
    @11
    @17
    @3
    @11
    @17
    @3
    @11
    wa
    #
    vz
    cA
    @5
    @16
    @11
    @5
    cA
    wfn
    #
    @3
    @6
    @8
    @20
    @10
    cA
    @4
    @5
    ffn
    3ad2ant1
    adantl
    @3
    @16
    cA
    wfn
    #
    @11
    @3
    cA
    @4
    @16
    wf
    #
    @21
    @3
    @15
    @4
    wcel
    #
    vx
    cA
    wral
    #
    @22
    @1
    @2
    @24
    @0
    @1
    @2
    wa
    @23
    vx
    cA
    @1
    @2
    @12
    cA
    wcel
    #
    @23
    @1
    @25
    wa
    @13
    cB
    wcel
    @14
    cC
    wcel
    @23
    @2
    @25
    wa
    cA
    cB
    @12
    cF
    ffvelrn
    cA
    cC
    @12
    cG
    ffvelrn
    @13
    @14
    cB
    cC
    opelxpi
    syl2an
    anandirs
    ralrimiva
    3adant1
    vx
    cA
    @4
    @15
    @16
    @16
    eqid
    #
    fmpt
    sylib
    #
    cA
    @4
    @16
    ffn
    syl
    #
    adantr
    @19
    vz
    cv
    #
    cA
    wcel
    #
    wa
    #
    @29
    @5
    cfv
    #
    @29
    cF
    cfv
    #
    @29
    cG
    cfv
    #
    cop
    #
    @29
    @16
    cfv
    #
    @31
    @32
    cvv
    cvv
    cxp
    #
    wcel
    #
    @32
    c1st
    cfv
    #
    @33
    wceq
    @32
    c2nd
    cfv
    #
    @34
    wceq
    @32
    @35
    wceq
    @11
    @30
    @38
    @3
    @6
    @8
    @30
    @38
    @10
    @6
    @30
    wa
    @4
    @37
    @32
    cB
    cC
    xpss
    cA
    @4
    @29
    @5
    ffvelrn
    #
    sseldi
    3ad2antl1
    adantll
    @31
    @33
    @29
    c1st
    @4
    cres
    #
    @5
    ccom
    #
    cfv
    #
    @32
    @42
    cfv
    #
    @39
    @11
    @33
    @44
    wceq
    #
    @3
    @30
    @8
    @6
    @46
    @10
    @8
    @33
    @29
    @7
    cfv
    @44
    @29
    cF
    @7
    fveq1
    @29
    @7
    @43
    cP
    @42
    @5
    upxp.1
    coeq1i
    fveq1i
    syl6eq
    3ad2ant2
    ad2antlr
    @19
    @6
    @30
    @44
    @45
    wceq
    @3
    @6
    @8
    @10
    simpr1
    #
    cA
    @4
    @29
    @42
    @5
    fvco3
    sylan
    @31
    @32
    @4
    wcel
    #
    @45
    @39
    wceq
    @11
    @30
    @48
    @3
    @6
    @8
    @30
    @48
    @10
    @41
    3ad2antl1
    adantll
    #
    @32
    @4
    c1st
    fvres
    syl
    3eqtrrd
    @31
    @34
    @29
    c2nd
    @4
    cres
    #
    @5
    ccom
    #
    cfv
    #
    @32
    @50
    cfv
    #
    @40
    @11
    @34
    @52
    wceq
    #
    @3
    @30
    @10
    @6
    @54
    @8
    @10
    @34
    @29
    @9
    cfv
    @52
    @29
    cG
    @9
    fveq1
    @29
    @9
    @51
    cQ
    @50
    @5
    upxp.2
    coeq1i
    fveq1i
    syl6eq
    3ad2ant3
    ad2antlr
    @19
    @6
    @30
    @52
    @53
    wceq
    @47
    cA
    @4
    @29
    @50
    @5
    fvco3
    sylan
    @31
    @48
    @53
    @40
    wceq
    @49
    @32
    @4
    c2nd
    fvres
    syl
    3eqtrrd
    @32
    @33
    @34
    cvv
    cvv
    eqopi
    syl12anc
    @30
    @36
    @35
    wceq
    #
    @19
    vx
    @29
    @15
    @35
    cA
    @16
    @12
    @29
    wceq
    @13
    @33
    @14
    @34
    @12
    @29
    cF
    fveq2
    @12
    @29
    cG
    fveq2
    opeq12d
    @26
    @33
    @34
    opex
    fvmpt
    #
    adantl
    eqtr4d
    eqfnfvd
    ex
    @3
    @11
    @17
    @22
    cF
    cP
    @16
    ccom
    #
    wceq
    #
    cG
    cQ
    @16
    ccom
    #
    wceq
    #
    w3a
    @3
    @22
    @58
    @60
    @27
    @3
    cF
    @42
    @16
    ccom
    #
    @57
    @3
    vz
    cA
    cF
    @61
    @1
    @0
    cF
    cA
    wfn
    @2
    cA
    cB
    cF
    ffn
    3ad2ant2
    @3
    @42
    @4
    wfn
    #
    @21
    @16
    crn
    @4
    wss
    #
    @61
    cA
    wfn
    @62
    @3
    c1st
    cvv
    wfn
    #
    @4
    cvv
    wss
    #
    @62
    cvv
    cvv
    c1st
    wfo
    @64
    fo1st
    cvv
    cvv
    c1st
    fofn
    ax-mp
    @4
    ssv
    #
    cvv
    @4
    c1st
    fnssres
    mp2an
    a1i
    @28
    @3
    @22
    @63
    @27
    cA
    @4
    @16
    frn
    syl
    #
    @4
    cA
    @42
    @16
    fnco
    syl3anc
    @3
    @30
    wa
    #
    @29
    @61
    cfv
    #
    @36
    @42
    cfv
    #
    @35
    @42
    cfv
    #
    @33
    @3
    @22
    @30
    @69
    @70
    wceq
    @27
    cA
    @4
    @29
    @42
    @16
    fvco3
    sylan
    @68
    @36
    @35
    @42
    @30
    @55
    @3
    @56
    adantl
    #
    fveq2d
    @68
    @71
    @35
    c1st
    cfv
    #
    @33
    @68
    @35
    @4
    wcel
    #
    @71
    @73
    wceq
    @1
    @2
    @30
    @74
    @0
    @1
    @2
    @30
    @74
    @1
    @30
    wa
    @33
    cB
    wcel
    @34
    cC
    wcel
    @74
    @2
    @30
    wa
    cA
    cB
    @29
    cF
    ffvelrn
    cA
    cC
    @29
    cG
    ffvelrn
    @33
    @34
    cB
    cC
    opelxpi
    syl2an
    anandirs
    3adantl1
    #
    @35
    @4
    c1st
    fvres
    syl
    @33
    @34
    @29
    cF
    fvex
    #
    @29
    cG
    fvex
    #
    op1st
    syl6eq
    3eqtrrd
    eqfnfvd
    cP
    @42
    @16
    upxp.1
    coeq1i
    syl6eqr
    @3
    cG
    @50
    @16
    ccom
    #
    @59
    @3
    vz
    cA
    cG
    @78
    @2
    @0
    cG
    cA
    wfn
    @1
    cA
    cC
    cG
    ffn
    3ad2ant3
    @3
    @50
    @4
    wfn
    #
    @21
    @63
    @78
    cA
    wfn
    @79
    @3
    c2nd
    cvv
    wfn
    #
    @65
    @79
    cvv
    cvv
    c2nd
    wfo
    @80
    fo2nd
    cvv
    cvv
    c2nd
    fofn
    ax-mp
    @66
    cvv
    @4
    c2nd
    fnssres
    mp2an
    a1i
    @28
    @67
    @4
    cA
    @50
    @16
    fnco
    syl3anc
    @68
    @29
    @78
    cfv
    #
    @36
    @50
    cfv
    #
    @35
    @50
    cfv
    #
    @34
    @3
    @22
    @30
    @81
    @82
    wceq
    @27
    cA
    @4
    @29
    @50
    @16
    fvco3
    sylan
    @68
    @36
    @35
    @50
    @72
    fveq2d
    @68
    @83
    @35
    c2nd
    cfv
    #
    @34
    @68
    @74
    @83
    @84
    wceq
    @75
    @35
    @4
    c2nd
    fvres
    syl
    @33
    @34
    @76
    @77
    op2nd
    syl6eq
    3eqtrrd
    eqfnfvd
    cQ
    @50
    @16
    upxp.2
    coeq1i
    syl6eqr
    3jca
    @17
    @6
    @22
    @8
    @58
    @10
    @60
    cA
    @4
    @5
    @16
    feq1
    @17
    @7
    @57
    cF
    @5
    @16
    cP
    coeq2
    eqeq2d
    @17
    @9
    @59
    cG
    @5
    @16
    cQ
    coeq2
    eqeq2d
    3anbi123d
    syl5ibrcom
    impbid
    eubidv
    mpbird
end
