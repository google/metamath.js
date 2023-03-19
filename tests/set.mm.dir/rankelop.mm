include "crnk.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "csuc.mm"
include "cop.mm"
include "rankelpr.mm"
include "word.mm"
include "wb.mm"
include "rankon.mm"
include "onordi.mm"
include "ordsucelsuc.mm"
include "ax-mp.mm"
include "sylib.mm"
include "cun.mm"
include "rankop.mm"
include "wceq.mm"
include "rankpr.mm"
include "suceq.mm"
include "eqtr4i.mm"
include "3eltr4g.mm"

theorem rankelop
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume rankelun.1: |- A e. _V
  assume rankelun.2: |- B e. _V
  assume rankelun.3: |- C e. _V
  assume rankelun.4: |- D e. _V


  assert |- ( ( ( rank ` A ) e. ( rank ` C ) /\ ( rank ` B ) e. ( rank ` D ) ) -> ( rank ` <. A , B >. ) e. ( rank ` <. C , D >. ) )

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
    cB
    crnk
    cfv
    #
    cD
    crnk
    cfv
    #
    wcel
    wa
    #
    cA
    cB
    cpr
    crnk
    cfv
    #
    csuc
    #
    cC
    cD
    cpr
    #
    crnk
    cfv
    #
    csuc
    #
    cA
    cB
    cop
    crnk
    cfv
    #
    cC
    cD
    cop
    crnk
    cfv
    #
    @4
    @5
    @8
    wcel
    #
    @6
    @9
    wcel
    #
    cA
    cB
    cC
    cD
    rankelun.1
    rankelun.2
    rankelun.3
    rankelun.4
    rankelpr
    @8
    word
    @12
    @13
    wb
    @8
    @7
    rankon
    onordi
    @5
    @8
    ordsucelsuc
    ax-mp
    sylib
    @10
    @0
    @2
    cun
    csuc
    #
    csuc
    #
    @6
    cA
    cB
    rankelun.1
    rankelun.2
    rankop
    @5
    @14
    wceq
    @6
    @15
    wceq
    cA
    cB
    rankelun.1
    rankelun.2
    rankpr
    @5
    @14
    suceq
    ax-mp
    eqtr4i
    @11
    @1
    @3
    cun
    csuc
    #
    csuc
    #
    @9
    cC
    cD
    rankelun.3
    rankelun.4
    rankop
    @8
    @16
    wceq
    @9
    @17
    wceq
    cC
    cD
    rankelun.3
    rankelun.4
    rankpr
    @8
    @16
    suceq
    ax-mp
    eqtr4i
    3eltr4g
end
