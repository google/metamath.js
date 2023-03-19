include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "cs4.mm"
include "ccnv.mm"
include "wfun.mm"
include "cc0.mm"
include "cop.mm"
include "c1.mm"
include "cpr.mm"
include "c2.mm"
include "c3.mm"
include "cun.mm"
include "cvv.mm"
include "c0ex.mm"
include "1ex.mm"
include "pm3.2i.mm"
include "2ex.mm"
include "3ex.mm"
include "a1i.mm"
include "funcnvqp.mm"
include "sylan.mm"
include "wceq.mm"
include "s4prop.mm"
include "adantr.mm"
include "cnveqd.mm"
include "funeqd.mm"
include "mpbird.mm"

theorem funcnvs4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V


  assert |- ( ( ( ( A e. V /\ B e. V ) /\ ( C e. V /\ D e. V ) ) /\ ( ( A =/= B /\ A =/= C /\ A =/= D ) /\ ( B =/= C /\ B =/= D ) /\ C =/= D ) ) -> Fun `' <" A B C D "> )

  proof
    cA
    cV
    wcel
    cB
    cV
    wcel
    wa
    cC
    cV
    wcel
    cD
    cV
    wcel
    wa
    wa
    #
    cA
    cB
    wne
    cA
    cC
    wne
    cA
    cD
    wne
    w3a
    cB
    cC
    wne
    cB
    cD
    wne
    wa
    cC
    cD
    wne
    w3a
    #
    wa
    #
    cA
    cB
    cC
    cD
    cs4
    #
    ccnv
    #
    wfun
    cc0
    cA
    cop
    c1
    cB
    cop
    cpr
    c2
    cC
    cop
    c3
    cD
    cop
    cpr
    cun
    #
    ccnv
    #
    wfun
    #
    @0
    cc0
    cvv
    wcel
    #
    c1
    cvv
    wcel
    #
    wa
    #
    c2
    cvv
    wcel
    #
    c3
    cvv
    wcel
    #
    wa
    #
    wa
    #
    @1
    @7
    @14
    @0
    @10
    @13
    @8
    @9
    c0ex
    1ex
    pm3.2i
    @11
    @12
    2ex
    3ex
    pm3.2i
    pm3.2i
    a1i
    cc0
    cA
    c1
    cB
    cvv
    cvv
    c2
    cC
    c3
    cD
    cvv
    cvv
    funcnvqp
    sylan
    @2
    @4
    @6
    @2
    @3
    @5
    @0
    @3
    @5
    wceq
    @1
    cA
    cB
    cC
    cD
    cV
    s4prop
    adantr
    cnveqd
    funeqd
    mpbird
end
