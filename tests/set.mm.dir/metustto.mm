include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "ccnv.mm"
include "cc0.mm"
include "cv.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "wceq.mm"
include "wa.mm"
include "wss.mm"
include "wo.mm"
include "crp.mm"
include "simpll.mm"
include "rpred.mm"
include "simplr.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "simpllr.mm"
include "cxr.mm"
include "0xr.mm"
include "a1i.mm"
include "simpl.mm"
include "rexrd.mm"
include "0le0.mm"
include "simpr.mm"
include "icossico.mm"
include "syl22anc.mm"
include "imass2.mm"
include "syl.mm"
include "sylancom.mm"
include "simplrl.mm"
include "simplrr.mm"
include "3sstr4d.mm"
include "orcd.mm"
include "simplll.mm"
include "olcd.mm"
include "lecasei.mm"
include "adantlll.mm"
include "wrex.mm"
include "metustel.mm"
include "biimpa.mm"
include "3adant3.mm"
include "cmpt.mm"
include "crn.mm"
include "oveq2.mm"
include "imaeq2d.mm"
include "cbvmptv.mm"
include "rneqi.mm"
include "eqtri.mm"
include "3adant2.mm"
include "reeanv.mm"
include "sylanbrc.mm"
include "r19.29vva.mm"

theorem metustto
  let cA: class A
  let cB: class B
  let cD: class D
  let cF: class F
  let cX: class X
  let va: setvar a
  let vb: setvar b
  assume metust.1: |- F = ran ( a e. RR+ |-> ( `' D " ( 0 [,) a ) ) )

  disjoint B a
  disjoint D a
  disjoint X a
  disjoint A a
  disjoint F a
  disjoint a b
  disjoint A b
  disjoint B b
  disjoint D b
  disjoint F b
  disjoint X b
  assert |- ( ( D e. ( PsMet ` X ) /\ A e. F /\ B e. F ) -> ( A C_ B \/ B C_ A ) )

  proof
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    cA
    cF
    wcel
    #
    cB
    cF
    wcel
    #
    w3a
    #
    cA
    cD
    ccnv
    #
    cc0
    va
    cv
    #
    cico
    co
    #
    cima
    #
    wceq
    #
    cB
    @4
    cc0
    vb
    cv
    #
    cico
    co
    #
    cima
    #
    wceq
    #
    wa
    #
    cA
    cB
    wss
    #
    cB
    cA
    wss
    #
    wo
    #
    va
    vb
    crp
    crp
    @5
    crp
    wcel
    #
    @9
    crp
    wcel
    #
    @13
    @16
    @3
    @17
    @18
    wa
    #
    @13
    wa
    #
    @16
    @5
    @9
    @20
    @5
    @17
    @18
    @13
    simpll
    rpred
    @20
    @9
    @17
    @18
    @13
    simplr
    rpred
    @20
    @5
    @9
    cle
    wbr
    #
    wa
    #
    @14
    @15
    @22
    @7
    @11
    cA
    cB
    @20
    @21
    @9
    cr
    wcel
    #
    @7
    @11
    wss
    #
    @22
    @9
    @17
    @18
    @13
    @21
    simpllr
    rpred
    @23
    @21
    wa
    #
    @6
    @10
    wss
    #
    @24
    @25
    cc0
    cxr
    wcel
    #
    @9
    cxr
    wcel
    cc0
    cc0
    cle
    wbr
    #
    @21
    @26
    @27
    @25
    0xr
    a1i
    @25
    @9
    @23
    @21
    simpl
    rexrd
    @28
    @25
    0le0
    a1i
    @23
    @21
    simpr
    cc0
    @9
    cc0
    @5
    icossico
    syl22anc
    @6
    @10
    @4
    imass2
    syl
    sylancom
    @19
    @8
    @12
    @21
    simplrl
    @19
    @8
    @12
    @21
    simplrr
    3sstr4d
    orcd
    @20
    @9
    @5
    cle
    wbr
    #
    wa
    #
    @15
    @14
    @30
    @11
    @7
    cB
    cA
    @20
    @29
    @5
    cr
    wcel
    #
    @11
    @7
    wss
    #
    @30
    @5
    @17
    @18
    @13
    @29
    simplll
    rpred
    @31
    @29
    wa
    #
    @10
    @6
    wss
    #
    @32
    @33
    @27
    @5
    cxr
    wcel
    @28
    @29
    @34
    @27
    @33
    0xr
    a1i
    @33
    @5
    @31
    @29
    simpl
    rexrd
    @28
    @33
    0le0
    a1i
    @31
    @29
    simpr
    cc0
    @5
    cc0
    @9
    icossico
    syl22anc
    @10
    @6
    @4
    imass2
    syl
    sylancom
    @19
    @8
    @12
    @29
    simplrr
    @19
    @8
    @12
    @29
    simplrl
    3sstr4d
    olcd
    lecasei
    adantlll
    @3
    @8
    va
    crp
    wrex
    #
    @12
    vb
    crp
    wrex
    #
    @13
    vb
    crp
    wrex
    va
    crp
    wrex
    @0
    @1
    @35
    @2
    @0
    @1
    @35
    cA
    cD
    cF
    cX
    va
    metust.1
    metustel
    biimpa
    3adant3
    @0
    @2
    @36
    @1
    @0
    @2
    @36
    cB
    cD
    cF
    cX
    vb
    cF
    va
    crp
    @7
    cmpt
    #
    crn
    vb
    crp
    @11
    cmpt
    #
    crn
    metust.1
    @37
    @38
    va
    vb
    crp
    @7
    @11
    @5
    @9
    wceq
    @6
    @10
    @4
    @5
    @9
    cc0
    cico
    oveq2
    imaeq2d
    cbvmptv
    rneqi
    eqtri
    metustel
    biimpa
    3adant2
    @8
    @12
    va
    vb
    crp
    crp
    reeanv
    sylanbrc
    r19.29vva
end
