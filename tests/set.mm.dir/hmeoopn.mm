include "chmeo.mm"
include "co.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cima.mm"
include "wi.mm"
include "hmeoima.mm"
include "ex.mm"
include "adantr.mm"
include "ccnv.mm"
include "ccn.mm"
include "hmeocn.mm"
include "cnima.mm"
include "syl.mm"
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

theorem hmeoopn
  let cA: class A
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  assume hmeoopn.1: |- X = U. J


  assert |- ( ( F e. ( J Homeo K ) /\ A C_ X ) -> ( A e. J <-> ( F " A ) e. K ) )

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
    wcel
    #
    cF
    cA
    cima
    #
    cK
    wcel
    #
    @0
    @3
    @5
    wi
    @1
    @0
    @3
    @5
    cA
    cF
    cJ
    cK
    hmeoima
    ex
    adantr
    @2
    @5
    cF
    ccnv
    @4
    cima
    #
    cJ
    wcel
    #
    @3
    @0
    @5
    @7
    wi
    #
    @1
    @0
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    @8
    cF
    cJ
    cK
    hmeocn
    @9
    @5
    @7
    @4
    cF
    cJ
    cK
    cnima
    ex
    syl
    adantr
    @2
    @6
    cA
    cJ
    @0
    cX
    cK
    cuni
    #
    cF
    wf1
    #
    @1
    @6
    cA
    wceq
    @0
    cX
    @10
    cF
    wf1o
    @11
    cF
    cJ
    cK
    cX
    @10
    hmeoopn.1
    @10
    eqid
    hmeof1o
    cX
    @10
    cF
    f1of1
    syl
    cX
    @10
    cA
    cF
    f1imacnv
    sylan
    eleq1d
    sylibd
    impbid
end
