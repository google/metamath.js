include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "cop.mm"
include "ovex.mm"
include "xpex.mm"
include "cv.mm"
include "wcel.mm"
include "wf.mm"
include "cfv.mm"
include "c1st.mm"
include "wa.mm"
include "elmap.mm"
include "ffvelrn.mm"
include "sylanb.mm"
include "xp1st.mm"
include "syl.mm"
include "fmptd.mm"
include "sylibr.mm"
include "c2nd.mm"
include "xp2nd.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "sylib.mm"
include "ffvelrnda.mm"
include "wceq.mm"
include "1st2nd2.mm"
include "ad2antlr.mm"
include "cmpt.mm"
include "feqmptd.mm"
include "simplr.mm"
include "fveq1d.mm"
include "cvv.mm"
include "opex.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "adantl.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "fvex.mm"
include "op1st.mm"
include "syl6eq.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "eqtr4d.mm"
include "op2nd.mm"
include "opeq12d.mm"
include "simpll.mm"
include "simpr.mm"
include "ad2antrr.mm"
include "op1stg.mm"
include "sylan9eq.mm"
include "op2ndg.mm"
include "impbida.mm"
include "en3i.mm"

theorem xpmapenlem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let vw: setvar w
  assume xpmapen.1: |- A e. _V
  assume xpmapen.2: |- B e. _V
  assume xpmapen.3: |- C e. _V
  assume xpmapenlem.4: |- D = ( z e. C |-> ( 1st ` ( x ` z ) ) )
  assume xpmapenlem.5: |- R = ( z e. C |-> ( 2nd ` ( x ` z ) ) )
  assume xpmapenlem.6: |- S = ( z e. C |-> <. ( ( 1st ` y ) ` z ) , ( ( 2nd ` y ) ` z ) >. )

  disjoint y z
  disjoint D y
  disjoint D z
  disjoint R y
  disjoint R z
  disjoint x z
  disjoint S x
  disjoint S z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint C w
  assert |- ( ( A X. B ) ^m C ) ~~ ( ( A ^m C ) X. ( B ^m C ) )

  proof
    vx
    vy
    cA
    cB
    cxp
    #
    cC
    cmap
    co
    #
    cA
    cC
    cmap
    co
    #
    cB
    cC
    cmap
    co
    #
    cxp
    #
    cD
    cR
    cop
    #
    cS
    @0
    cC
    cmap
    ovex
    @2
    @3
    cA
    cC
    cmap
    ovex
    cB
    cC
    cmap
    ovex
    xpex
    vx
    cv
    #
    @1
    wcel
    #
    cD
    @2
    wcel
    #
    cR
    @3
    wcel
    #
    @5
    @4
    wcel
    @7
    cC
    cA
    cD
    wf
    @8
    @7
    vz
    cC
    vz
    cv
    #
    @6
    cfv
    #
    c1st
    cfv
    #
    cA
    cD
    @7
    @10
    cC
    wcel
    #
    wa
    #
    @11
    @0
    wcel
    #
    @12
    cA
    wcel
    @7
    cC
    @0
    @6
    wf
    #
    @13
    @15
    @0
    cC
    @6
    cA
    cB
    xpmapen.1
    xpmapen.2
    xpex
    #
    xpmapen.3
    elmap
    #
    cC
    @0
    @10
    @6
    ffvelrn
    sylanb
    #
    @11
    cA
    cB
    xp1st
    syl
    xpmapenlem.4
    fmptd
    cA
    cC
    cD
    xpmapen.1
    xpmapen.3
    elmap
    sylibr
    #
    @7
    cC
    cB
    cR
    wf
    @9
    @7
    vz
    cC
    @11
    c2nd
    cfv
    #
    cB
    cR
    @14
    @15
    @21
    cB
    wcel
    @19
    @11
    cA
    cB
    xp2nd
    syl
    xpmapenlem.5
    fmptd
    cB
    cC
    cR
    xpmapen.2
    xpmapen.3
    elmap
    sylibr
    #
    cD
    cR
    @2
    @3
    opelxpi
    syl2anc
    vy
    cv
    #
    @4
    wcel
    #
    cC
    @0
    cS
    wf
    cS
    @1
    wcel
    @24
    vz
    cC
    @10
    @23
    c1st
    cfv
    #
    cfv
    #
    @10
    @23
    c2nd
    cfv
    #
    cfv
    #
    cop
    #
    @0
    cS
    @24
    @13
    wa
    @26
    cA
    wcel
    @28
    cB
    wcel
    @29
    @0
    wcel
    @24
    cC
    cA
    @10
    @25
    @24
    @25
    @2
    wcel
    cC
    cA
    @25
    wf
    @23
    @2
    @3
    xp1st
    cA
    cC
    @25
    xpmapen.1
    xpmapen.3
    elmap
    sylib
    #
    ffvelrnda
    @24
    cC
    cB
    @10
    @27
    @24
    @27
    @3
    wcel
    cC
    cB
    @27
    wf
    @23
    @2
    @3
    xp2nd
    cB
    cC
    @27
    xpmapen.2
    xpmapen.3
    elmap
    sylib
    #
    ffvelrnda
    @26
    @28
    cA
    cB
    opelxpi
    syl2anc
    xpmapenlem.6
    fmptd
    @0
    cC
    cS
    @17
    xpmapen.3
    elmap
    sylibr
    @7
    @24
    wa
    #
    @6
    cS
    wceq
    #
    @23
    @5
    wceq
    #
    @32
    @33
    wa
    #
    @23
    @25
    @27
    cop
    #
    @5
    @24
    @23
    @36
    wceq
    @7
    @33
    @23
    @2
    @3
    1st2nd2
    ad2antlr
    @35
    @25
    cD
    @27
    cR
    @35
    @25
    vz
    cC
    @26
    cmpt
    #
    cD
    @24
    @25
    @37
    wceq
    @7
    @33
    @24
    vz
    cC
    cA
    @25
    @30
    feqmptd
    ad2antlr
    @35
    cD
    vz
    cC
    @12
    cmpt
    @37
    xpmapenlem.4
    @35
    vz
    cC
    @12
    @26
    @35
    @13
    wa
    #
    @12
    @29
    c1st
    cfv
    @26
    @38
    @11
    @29
    c1st
    @38
    @11
    @10
    cS
    cfv
    #
    @29
    @38
    @10
    @6
    cS
    @32
    @33
    @13
    simplr
    fveq1d
    @13
    @39
    @29
    wceq
    #
    @35
    @13
    @29
    cvv
    wcel
    @40
    @26
    @28
    opex
    vz
    cC
    @29
    cvv
    cS
    xpmapenlem.6
    fvmpt2
    mpan2
    adantl
    eqtrd
    #
    fveq2d
    @26
    @28
    @10
    @25
    fvex
    #
    @10
    @27
    fvex
    #
    op1st
    syl6eq
    mpteq2dva
    syl5eq
    eqtr4d
    @35
    @27
    vz
    cC
    @28
    cmpt
    #
    cR
    @24
    @27
    @44
    wceq
    @7
    @33
    @24
    vz
    cC
    cB
    @27
    @31
    feqmptd
    ad2antlr
    @35
    cR
    vz
    cC
    @21
    cmpt
    @44
    xpmapenlem.5
    @35
    vz
    cC
    @21
    @28
    @38
    @21
    @29
    c2nd
    cfv
    @28
    @38
    @11
    @29
    c2nd
    @41
    fveq2d
    @26
    @28
    @42
    @43
    op2nd
    syl6eq
    mpteq2dva
    syl5eq
    eqtr4d
    opeq12d
    eqtrd
    @32
    @34
    wa
    #
    @6
    vz
    cC
    @11
    cmpt
    #
    cS
    @45
    vz
    cC
    @0
    @6
    @45
    @7
    @16
    @7
    @24
    @34
    simpll
    @18
    sylib
    #
    feqmptd
    @45
    cS
    vz
    cC
    @29
    cmpt
    @46
    xpmapenlem.6
    @45
    vz
    cC
    @29
    @11
    @45
    @13
    wa
    #
    @29
    @12
    @21
    cop
    #
    @11
    @48
    @26
    @12
    @28
    @21
    @45
    @13
    @26
    @10
    cD
    cfv
    #
    @12
    @45
    @10
    @25
    cD
    @45
    @25
    @5
    c1st
    cfv
    #
    cD
    @45
    @23
    @5
    c1st
    @32
    @34
    simpr
    #
    fveq2d
    @45
    @8
    @9
    @51
    cD
    wceq
    @7
    @8
    @24
    @34
    @20
    ad2antrr
    #
    @7
    @9
    @24
    @34
    @22
    ad2antrr
    #
    cD
    cR
    @2
    @3
    op1stg
    syl2anc
    eqtrd
    fveq1d
    @13
    @12
    cvv
    wcel
    @50
    @12
    wceq
    @11
    c1st
    fvex
    vz
    cC
    @12
    cvv
    cD
    xpmapenlem.4
    fvmpt2
    mpan2
    sylan9eq
    @45
    @13
    @28
    @10
    cR
    cfv
    #
    @21
    @45
    @10
    @27
    cR
    @45
    @27
    @5
    c2nd
    cfv
    #
    cR
    @45
    @23
    @5
    c2nd
    @52
    fveq2d
    @45
    @8
    @9
    @56
    cR
    wceq
    @53
    @54
    cD
    cR
    @2
    @3
    op2ndg
    syl2anc
    eqtrd
    fveq1d
    @13
    @21
    cvv
    wcel
    @55
    @21
    wceq
    @11
    c2nd
    fvex
    vz
    cC
    @21
    cvv
    cR
    xpmapenlem.5
    fvmpt2
    mpan2
    sylan9eq
    opeq12d
    @48
    @15
    @11
    @49
    wceq
    @45
    cC
    @0
    @10
    @6
    @47
    ffvelrnda
    @11
    cA
    cB
    1st2nd2
    syl
    eqtr4d
    mpteq2dva
    syl5eq
    eqtr4d
    impbida
    en3i
end
