include "cgim.mm"
include "co.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "csubg.mm"
include "cfv.mm"
include "cima.mm"
include "cghm.mm"
include "gimghm.mm"
include "adantr.mm"
include "ghmima.mm"
include "sylan.mm"
include "ccnv.mm"
include "wceq.mm"
include "cbs.mm"
include "wf1.mm"
include "wf1o.mm"
include "eqid.mm"
include "gimf1o.mm"
include "f1of1.mm"
include "syl.mm"
include "f1imacnv.mm"
include "ghmpreima.mm"
include "eqeltrrd.mm"
include "impbida.mm"

theorem subggim
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  assume subgim.b: |- B = ( Base ` R )


  assert |- ( ( F e. ( R GrpIso S ) /\ A C_ B ) -> ( A e. ( SubGrp ` R ) <-> ( F " A ) e. ( SubGrp ` S ) ) )

  proof
    cF
    cR
    cS
    cgim
    co
    wcel
    #
    cA
    cB
    wss
    #
    wa
    #
    cA
    cR
    csubg
    cfv
    #
    wcel
    #
    cF
    cA
    cima
    #
    cS
    csubg
    cfv
    wcel
    #
    @2
    cF
    cR
    cS
    cghm
    co
    wcel
    #
    @4
    @6
    @0
    @7
    @1
    cR
    cS
    cF
    gimghm
    adantr
    #
    cR
    cS
    cA
    cF
    ghmima
    sylan
    @2
    @6
    wa
    cF
    ccnv
    @5
    cima
    #
    cA
    @3
    @2
    @9
    cA
    wceq
    #
    @6
    @0
    cB
    cS
    cbs
    cfv
    #
    cF
    wf1
    #
    @1
    @10
    @0
    cB
    @11
    cF
    wf1o
    @12
    cB
    @11
    cR
    cS
    cF
    subgim.b
    @11
    eqid
    gimf1o
    cB
    @11
    cF
    f1of1
    syl
    cB
    @11
    cA
    cF
    f1imacnv
    sylan
    adantr
    @2
    @7
    @6
    @9
    @3
    wcel
    @8
    cR
    cS
    cF
    @5
    ghmpreima
    sylan
    eqeltrrd
    impbida
end
