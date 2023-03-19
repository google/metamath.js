include "cop.mm"
include "cltpq.mm"
include "wbr.mm"
include "cnpi.mm"
include "cxp.mm"
include "wcel.mm"
include "wa.mm"
include "cmi.mm"
include "co.mm"
include "clti.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "opex.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "fveq2.mm"
include "opelxp.mm"
include "op1stg.mm"
include "sylbi.mm"
include "adantr.mm"
include "sylan9eq.mm"
include "oveq1d.mm"
include "op2ndg.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "pm5.32da.mm"
include "bitrd.mm"
include "anbi2d.mm"
include "adantl.mm"
include "df-ltpq.mm"
include "brab.mm"
include "simpr.mm"
include "ltrelpi.mm"
include "brel.mm"
include "dmmulpi.mm"
include "0npi.mm"
include "ndmovrcl.mm"
include "anim12i.mm"
include "opelxpi.mm"
include "ad2ant2rl.mm"
include "simprl.mm"
include "simplr.mm"
include "syl2anc.mm"
include "jca.mm"
include "3syl.mm"
include "ancri.mm"
include "impbii.mm"
include "bitri.mm"

theorem ordpipq
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y


  assert |- ( <. A , B >. <pQ <. C , D >. <-> ( A .N D ) <N ( C .N B ) )

  proof
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    cltpq
    wbr
    @0
    cnpi
    cnpi
    cxp
    #
    wcel
    #
    @1
    @2
    wcel
    #
    wa
    #
    cA
    cD
    cmi
    co
    #
    cC
    cB
    cmi
    co
    #
    clti
    wbr
    #
    wa
    #
    @8
    vx
    cv
    #
    @2
    wcel
    #
    vy
    cv
    #
    @2
    wcel
    #
    wa
    #
    @10
    c1st
    cfv
    #
    @12
    c2nd
    cfv
    #
    cmi
    co
    #
    @12
    c1st
    cfv
    #
    @10
    c2nd
    cfv
    #
    cmi
    co
    #
    clti
    wbr
    #
    wa
    #
    @3
    @13
    wa
    #
    cA
    @16
    cmi
    co
    #
    @18
    cB
    cmi
    co
    #
    clti
    wbr
    #
    wa
    #
    @9
    vx
    vy
    @0
    @1
    cltpq
    cA
    cB
    opex
    cC
    cD
    opex
    @10
    @0
    wceq
    #
    @22
    @23
    @21
    wa
    @27
    @28
    @14
    @23
    @21
    @28
    @11
    @3
    @13
    @10
    @0
    @2
    eleq1
    anbi1d
    anbi1d
    @28
    @23
    @21
    @26
    @28
    @23
    wa
    #
    @17
    @24
    @20
    @25
    clti
    @29
    @15
    cA
    @16
    cmi
    @28
    @23
    @15
    @0
    c1st
    cfv
    #
    cA
    @10
    @0
    c1st
    fveq2
    @3
    @30
    cA
    wceq
    #
    @13
    @3
    cA
    cnpi
    wcel
    #
    cB
    cnpi
    wcel
    #
    wa
    #
    @31
    cA
    cB
    cnpi
    cnpi
    opelxp
    #
    cA
    cB
    cnpi
    cnpi
    op1stg
    sylbi
    adantr
    sylan9eq
    oveq1d
    @29
    @19
    cB
    @18
    cmi
    @28
    @23
    @19
    @0
    c2nd
    cfv
    #
    cB
    @10
    @0
    c2nd
    fveq2
    @3
    @36
    cB
    wceq
    #
    @13
    @3
    @34
    @37
    @35
    cA
    cB
    cnpi
    cnpi
    op2ndg
    sylbi
    adantr
    sylan9eq
    oveq2d
    breq12d
    pm5.32da
    bitrd
    @12
    @1
    wceq
    #
    @27
    @5
    @26
    wa
    @9
    @38
    @23
    @5
    @26
    @38
    @13
    @4
    @3
    @12
    @1
    @2
    eleq1
    anbi2d
    anbi1d
    @38
    @5
    @26
    @8
    @38
    @5
    wa
    #
    @24
    @6
    @25
    @7
    clti
    @39
    @16
    cD
    cA
    cmi
    @38
    @5
    @16
    @1
    c2nd
    cfv
    #
    cD
    @12
    @1
    c2nd
    fveq2
    @4
    @40
    cD
    wceq
    #
    @3
    @4
    cC
    cnpi
    wcel
    #
    cD
    cnpi
    wcel
    #
    wa
    #
    @41
    cC
    cD
    cnpi
    cnpi
    opelxp
    #
    cC
    cD
    cnpi
    cnpi
    op2ndg
    sylbi
    adantl
    sylan9eq
    oveq2d
    @39
    @18
    cC
    cB
    cmi
    @38
    @5
    @18
    @1
    c1st
    cfv
    #
    cC
    @12
    @1
    c1st
    fveq2
    @4
    @46
    cC
    wceq
    #
    @3
    @4
    @44
    @47
    @45
    cC
    cD
    cnpi
    cnpi
    op1stg
    sylbi
    adantl
    sylan9eq
    oveq1d
    breq12d
    pm5.32da
    bitrd
    vx
    vy
    df-ltpq
    brab
    @9
    @8
    @5
    @8
    simpr
    @8
    @5
    @8
    @6
    cnpi
    wcel
    #
    @7
    cnpi
    wcel
    #
    wa
    @32
    @43
    wa
    #
    @42
    @33
    wa
    #
    wa
    #
    @5
    @6
    @7
    cnpi
    cnpi
    clti
    ltrelpi
    brel
    @48
    @50
    @49
    @51
    cA
    cD
    cnpi
    cmi
    dmmulpi
    0npi
    ndmovrcl
    cC
    cB
    cnpi
    cmi
    dmmulpi
    0npi
    ndmovrcl
    anim12i
    @52
    @3
    @4
    @32
    @33
    @3
    @43
    @42
    cA
    cB
    cnpi
    cnpi
    opelxpi
    ad2ant2rl
    @52
    @42
    @43
    @4
    @50
    @42
    @33
    simprl
    @32
    @43
    @51
    simplr
    cC
    cD
    cnpi
    cnpi
    opelxpi
    syl2anc
    jca
    3syl
    ancri
    impbii
    bitri
end
