include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "cn.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "wceq.mm"
include "eqtr2.mm"
include "wb.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr1.mm"
include "brcgr.mm"
include "syl22anc.mm"
include "simpr2.mm"
include "simpr3.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "mpbiri.mm"
include "3adant1.mm"

theorem axcgrtr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cN: class N
  let vi: setvar i


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\ ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) -> ( ( <. A , B >. Cgr <. C , D >. /\ <. A , B >. Cgr <. E , F >. ) -> <. C , D >. Cgr <. E , F >. ) )

  proof
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cC
    @0
    wcel
    #
    w3a
    #
    cD
    @0
    wcel
    #
    cE
    @0
    wcel
    #
    cF
    @0
    wcel
    #
    w3a
    #
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    ccgr
    wbr
    #
    @9
    cE
    cF
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    @10
    @12
    ccgr
    wbr
    #
    wi
    #
    cN
    cn
    wcel
    @4
    @8
    wa
    #
    @16
    c1
    cN
    cfz
    co
    #
    vi
    cv
    #
    cA
    cfv
    @19
    cB
    cfv
    cmin
    co
    c2
    cexp
    co
    vi
    csu
    #
    @18
    @19
    cC
    cfv
    @19
    cD
    cfv
    cmin
    co
    c2
    cexp
    co
    vi
    csu
    #
    wceq
    #
    @20
    @18
    @19
    cE
    cfv
    @19
    cF
    cfv
    cmin
    co
    c2
    cexp
    co
    vi
    csu
    #
    wceq
    #
    wa
    #
    @21
    @23
    wceq
    #
    wi
    @20
    @21
    @23
    eqtr2
    @17
    @14
    @25
    @15
    @26
    @17
    @11
    @22
    @13
    @24
    @17
    @1
    @2
    @3
    @5
    @11
    @22
    wb
    @1
    @2
    @3
    @8
    simpl1
    #
    @1
    @2
    @3
    @8
    simpl2
    #
    @1
    @2
    @3
    @8
    simpl3
    #
    @4
    @5
    @6
    @7
    simpr1
    #
    cA
    cB
    cC
    cD
    vi
    cN
    brcgr
    syl22anc
    @17
    @1
    @2
    @6
    @7
    @13
    @24
    wb
    @27
    @28
    @4
    @5
    @6
    @7
    simpr2
    #
    @4
    @5
    @6
    @7
    simpr3
    #
    cA
    cB
    cE
    cF
    vi
    cN
    brcgr
    syl22anc
    anbi12d
    @17
    @3
    @5
    @6
    @7
    @15
    @26
    wb
    @29
    @30
    @31
    @32
    cC
    cD
    cE
    cF
    vi
    cN
    brcgr
    syl22anc
    imbi12d
    mpbiri
    3adant1
end
