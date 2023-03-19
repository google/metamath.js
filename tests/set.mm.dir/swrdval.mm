include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cop.mm"
include "cvv.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cfzo.mm"
include "co.mm"
include "cdm.mm"
include "wss.mm"
include "cc0.mm"
include "cmin.mm"
include "caddc.mm"
include "cmpt.mm"
include "c0.mm"
include "cif.mm"
include "csubstr.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-substr.mm"
include "a1i.mm"
include "wa.mm"
include "simprl.mm"
include "fveq2.mm"
include "adantl.mm"
include "op1stg.mm"
include "3adant1.mm"
include "sylan9eqr.mm"
include "op2ndg.mm"
include "simp2.mm"
include "simp3.mm"
include "oveq12d.mm"
include "simp1.mm"
include "dmeqd.mm"
include "sseq12d.mm"
include "oveq2d.mm"
include "fveq12d.mm"
include "mpteq12dv.mm"
include "ifbieq1d.mm"
include "syl3anc.mm"
include "elex.mm"
include "3ad2ant1.mm"
include "opelxpi.mm"
include "ovex.mm"
include "mptex.mm"
include "0ex.mm"
include "ifex.mm"
include "ovmpt2d.mm"

theorem swrdval
  let vx: setvar x
  let cS: class S
  let cF: class F
  let cL: class L
  let cV: class V
  let vb: setvar b
  let vs: setvar s
  let cA: class A
  let cX: class X

  disjoint S x
  disjoint F x
  disjoint L x
  disjoint V x
  disjoint b s
  disjoint s x
  disjoint S s
  disjoint b x
  disjoint S b
  disjoint F s
  disjoint F b
  disjoint L s
  disjoint L b
  disjoint V s
  disjoint V b
  disjoint A s
  disjoint A b
  disjoint A x
  disjoint X x
  assert |- ( ( S e. V /\ F e. ZZ /\ L e. ZZ ) -> ( S substr <. F , L >. ) = if ( ( F ..^ L ) C_ dom S , ( x e. ( 0 ..^ ( L - F ) ) |-> ( S ` ( x + F ) ) ) , (/) ) )

  proof
    cS
    cV
    wcel
    #
    cF
    cz
    wcel
    #
    cL
    cz
    wcel
    #
    w3a
    #
    vs
    vb
    cS
    cF
    cL
    cop
    #
    cvv
    cz
    cz
    cxp
    #
    vb
    cv
    #
    c1st
    cfv
    #
    @6
    c2nd
    cfv
    #
    cfzo
    co
    #
    vs
    cv
    #
    cdm
    #
    wss
    #
    vx
    cc0
    @8
    @7
    cmin
    co
    #
    cfzo
    co
    #
    vx
    cv
    #
    @7
    caddc
    co
    #
    @10
    cfv
    #
    cmpt
    #
    c0
    cif
    #
    cF
    cL
    cfzo
    co
    #
    cS
    cdm
    #
    wss
    #
    vx
    cc0
    cL
    cF
    cmin
    co
    #
    cfzo
    co
    #
    @15
    cF
    caddc
    co
    #
    cS
    cfv
    #
    cmpt
    #
    c0
    cif
    #
    csubstr
    cvv
    csubstr
    vs
    vb
    cvv
    @5
    @19
    cmpt2
    wceq
    @3
    vx
    vs
    vb
    df-substr
    a1i
    @3
    @10
    cS
    wceq
    #
    @6
    @4
    wceq
    #
    wa
    #
    wa
    @29
    @7
    cF
    wceq
    #
    @8
    cL
    wceq
    #
    @19
    @28
    wceq
    @3
    @29
    @30
    simprl
    @31
    @3
    @7
    @4
    c1st
    cfv
    #
    cF
    @30
    @7
    @34
    wceq
    @29
    @6
    @4
    c1st
    fveq2
    adantl
    @1
    @2
    @34
    cF
    wceq
    @0
    cF
    cL
    cz
    cz
    op1stg
    3adant1
    sylan9eqr
    @31
    @3
    @8
    @4
    c2nd
    cfv
    #
    cL
    @30
    @8
    @35
    wceq
    @29
    @6
    @4
    c2nd
    fveq2
    adantl
    @1
    @2
    @35
    cL
    wceq
    @0
    cF
    cL
    cz
    cz
    op2ndg
    3adant1
    sylan9eqr
    @29
    @32
    @33
    w3a
    #
    @12
    @22
    @18
    @27
    c0
    @36
    @9
    @20
    @11
    @21
    @36
    @7
    cF
    @8
    cL
    cfzo
    @29
    @32
    @33
    simp2
    #
    @29
    @32
    @33
    simp3
    #
    oveq12d
    @36
    @10
    cS
    @29
    @32
    @33
    simp1
    #
    dmeqd
    sseq12d
    @36
    vx
    @14
    @17
    @24
    @26
    @36
    @13
    @23
    cc0
    cfzo
    @36
    @8
    cL
    @7
    cF
    cmin
    @38
    @37
    oveq12d
    oveq2d
    @36
    @16
    @25
    @10
    cS
    @39
    @36
    @7
    cF
    @15
    caddc
    @37
    oveq2d
    fveq12d
    mpteq12dv
    ifbieq1d
    syl3anc
    @0
    @1
    cS
    cvv
    wcel
    @2
    cS
    cV
    elex
    3ad2ant1
    @1
    @2
    @4
    @5
    wcel
    @0
    cF
    cL
    cz
    cz
    opelxpi
    3adant1
    @28
    cvv
    wcel
    @3
    @22
    @27
    c0
    vx
    @24
    @26
    cc0
    @23
    cfzo
    ovex
    mptex
    0ex
    ifex
    a1i
    ovmpt2d
end
