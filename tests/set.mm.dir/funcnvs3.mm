include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "cs3.mm"
include "ccnv.mm"
include "wfun.mm"
include "cc0.mm"
include "cop.mm"
include "c1.mm"
include "c2.mm"
include "ctp.mm"
include "cvv.mm"
include "c0ex.mm"
include "1ex.mm"
include "2ex.mm"
include "3pm3.2i.mm"
include "a1i.mm"
include "funcnvtp.mm"
include "sylan.mm"
include "wceq.mm"
include "s3tpop.mm"
include "adantr.mm"
include "cnveqd.mm"
include "funeqd.mm"
include "mpbird.mm"

theorem funcnvs3
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V


  assert |- ( ( ( A e. V /\ B e. V /\ C e. V ) /\ ( A =/= B /\ A =/= C /\ B =/= C ) ) -> Fun `' <" A B C "> )

  proof
    cA
    cV
    wcel
    cB
    cV
    wcel
    cC
    cV
    wcel
    w3a
    #
    cA
    cB
    wne
    cA
    cC
    wne
    cB
    cC
    wne
    w3a
    #
    wa
    #
    cA
    cB
    cC
    cs3
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
    c2
    cC
    cop
    ctp
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
    c2
    cvv
    wcel
    #
    w3a
    #
    @1
    @7
    @11
    @0
    @8
    @9
    @10
    c0ex
    1ex
    2ex
    3pm3.2i
    a1i
    cc0
    cA
    c1
    cB
    cvv
    c2
    cC
    cvv
    cvv
    funcnvtp
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
    cV
    s3tpop
    adantr
    cnveqd
    funeqd
    mpbird
end
