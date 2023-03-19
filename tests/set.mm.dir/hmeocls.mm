include "chmeo.mm"
include "co.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cima.mm"
include "ccl.mm"
include "cfv.mm"
include "ccnv.mm"
include "ccn.mm"
include "hmeocnvcn.mm"
include "cncls2i.mm"
include "sylan.mm"
include "imacnvcnv.mm"
include "fveq2i.mm"
include "3sstr3g.mm"
include "hmeocn.mm"
include "cnclsi.mm"
include "eqssd.mm"

theorem hmeocls
  let cA: class A
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  assume hmeoopn.1: |- X = U. J


  assert |- ( ( F e. ( J Homeo K ) /\ A C_ X ) -> ( ( cls ` K ) ` ( F " A ) ) = ( F " ( ( cls ` J ) ` A ) ) )

  proof
    cF
    cJ
    cK
    chmeo
    co
    wcel
    #
    cA
    cX
    wss
    #
    wa
    #
    cF
    cA
    cima
    #
    cK
    ccl
    cfv
    #
    cfv
    #
    cF
    cA
    cJ
    ccl
    cfv
    cfv
    #
    cima
    #
    @2
    cF
    ccnv
    #
    ccnv
    #
    cA
    cima
    #
    @4
    cfv
    #
    @9
    @6
    cima
    #
    @5
    @7
    @0
    @8
    cK
    cJ
    ccn
    co
    wcel
    @1
    @11
    @12
    wss
    cF
    cJ
    cK
    hmeocnvcn
    cA
    @8
    cK
    cJ
    cX
    hmeoopn.1
    cncls2i
    sylan
    @10
    @3
    @4
    cF
    cA
    imacnvcnv
    fveq2i
    cF
    @6
    imacnvcnv
    3sstr3g
    @0
    cF
    cJ
    cK
    ccn
    co
    wcel
    @1
    @7
    @5
    wss
    cF
    cJ
    cK
    hmeocn
    cA
    cF
    cJ
    cK
    cX
    hmeoopn.1
    cnclsi
    sylan
    eqssd
end
