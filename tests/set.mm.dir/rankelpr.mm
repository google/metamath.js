include "crnk.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cun.mm"
include "csuc.mm"
include "cpr.mm"
include "rankelun.mm"
include "rankun.mm"
include "3eltr3g.mm"
include "word.mm"
include "wb.mm"
include "rankon.mm"
include "onun2i.mm"
include "onordi.mm"
include "ordsucelsuc.mm"
include "ax-mp.mm"
include "sylib.mm"
include "rankpr.mm"
include "3eltr4g.mm"

theorem rankelpr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume rankelun.1: |- A e. _V
  assume rankelun.2: |- B e. _V
  assume rankelun.3: |- C e. _V
  assume rankelun.4: |- D e. _V


  assert |- ( ( ( rank ` A ) e. ( rank ` C ) /\ ( rank ` B ) e. ( rank ` D ) ) -> ( rank ` { A , B } ) e. ( rank ` { C , D } ) )

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
    @0
    @2
    cun
    #
    csuc
    #
    @1
    @3
    cun
    #
    csuc
    #
    cA
    cB
    cpr
    crnk
    cfv
    cC
    cD
    cpr
    crnk
    cfv
    @4
    @5
    @7
    wcel
    #
    @6
    @8
    wcel
    #
    @4
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
    @5
    @7
    cA
    cB
    cC
    cD
    rankelun.1
    rankelun.2
    rankelun.3
    rankelun.4
    rankelun
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
    3eltr3g
    @7
    word
    @9
    @10
    wb
    @7
    @1
    @3
    cC
    rankon
    cD
    rankon
    onun2i
    onordi
    @5
    @7
    ordsucelsuc
    ax-mp
    sylib
    cA
    cB
    rankelun.1
    rankelun.2
    rankpr
    cC
    cD
    rankelun.3
    rankelun.4
    rankpr
    3eltr4g
end
