include "chmeo.mm"
include "co.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccld.mm"
include "cfv.mm"
include "cima.mm"
include "ccnv.mm"
include "ccn.mm"
include "wi.mm"
include "hmeocnvcn.mm"
include "adantr.mm"
include "imacnvcnv.mm"
include "cnclima.mm"
include "syl5eqelr.mm"
include "ex.mm"
include "syl.mm"
include "hmeocn.mm"
include "cuni.mm"
include "wf1.mm"
include "wceq.mm"
include "wf1o.mm"
include "eqid.mm"
include "hmeof1o.mm"
include "f1of1.mm"
include "f1imacnv.mm"
include "sylan.mm"
include "eleq1d.mm"
include "sylibd.mm"
include "impbid.mm"

theorem hmeocld
  let cA: class A
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  assume hmeoopn.1: |- X = U. J


  assert |- ( ( F e. ( J Homeo K ) /\ A C_ X ) -> ( A e. ( Clsd ` J ) <-> ( F " A ) e. ( Clsd ` K ) ) )

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
    cA
    cJ
    ccld
    cfv
    #
    wcel
    #
    cF
    cA
    cima
    #
    cK
    ccld
    cfv
    #
    wcel
    #
    @2
    cF
    ccnv
    #
    cK
    cJ
    ccn
    co
    wcel
    #
    @4
    @7
    wi
    @0
    @9
    @1
    cF
    cJ
    cK
    hmeocnvcn
    adantr
    @9
    @4
    @7
    @9
    @4
    wa
    @5
    @8
    ccnv
    cA
    cima
    @6
    cF
    cA
    imacnvcnv
    cA
    @8
    cK
    cJ
    cnclima
    syl5eqelr
    ex
    syl
    @2
    @7
    @8
    @5
    cima
    #
    @3
    wcel
    #
    @4
    @2
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    @7
    @11
    wi
    @0
    @12
    @1
    cF
    cJ
    cK
    hmeocn
    adantr
    @12
    @7
    @11
    @5
    cF
    cJ
    cK
    cnclima
    ex
    syl
    @2
    @10
    cA
    @3
    @0
    cX
    cK
    cuni
    #
    cF
    wf1
    #
    @1
    @10
    cA
    wceq
    @0
    cX
    @13
    cF
    wf1o
    @14
    cF
    cJ
    cK
    cX
    @13
    hmeoopn.1
    @13
    eqid
    hmeof1o
    cX
    @13
    cF
    f1of1
    syl
    cX
    @13
    cA
    cF
    f1imacnv
    sylan
    eleq1d
    sylibd
    impbid
end
