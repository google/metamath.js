include "crnk.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cun.mm"
include "word.mm"
include "rankon.mm"
include "onun2i.mm"
include "onordi.mm"
include "a1i.mm"
include "elun1.mm"
include "adantr.mm"
include "elun2.mm"
include "adantl.mm"
include "ordunel.mm"
include "syl3anc.mm"
include "rankun.mm"
include "3eltr4g.mm"

theorem rankelun
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume rankelun.1: |- A e. _V
  assume rankelun.2: |- B e. _V
  assume rankelun.3: |- C e. _V
  assume rankelun.4: |- D e. _V


  assert |- ( ( ( rank ` A ) e. ( rank ` C ) /\ ( rank ` B ) e. ( rank ` D ) ) -> ( rank ` ( A u. B ) ) e. ( rank ` ( C u. D ) ) )

  proof
    cA
    crnk
    cfv
    #
    cC
    crnk
    cfv
    #
    wcel
    #
    cB
    crnk
    cfv
    #
    cD
    crnk
    cfv
    #
    wcel
    #
    wa
    #
    @0
    @3
    cun
    #
    @1
    @4
    cun
    #
    cA
    cB
    cun
    crnk
    cfv
    cC
    cD
    cun
    crnk
    cfv
    @6
    @8
    word
    #
    @0
    @8
    wcel
    #
    @3
    @8
    wcel
    #
    @7
    @8
    wcel
    @9
    @6
    @8
    @1
    @4
    cC
    rankon
    cD
    rankon
    onun2i
    onordi
    a1i
    @2
    @10
    @5
    @0
    @1
    @4
    elun1
    adantr
    @5
    @11
    @2
    @3
    @4
    @1
    elun2
    adantl
    @8
    @0
    @3
    ordunel
    syl3anc
    cA
    cB
    rankelun.1
    rankelun.2
    rankun
    cC
    cD
    rankelun.3
    rankelun.4
    rankun
    3eltr4g
end
