include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cun.mm"
include "wceq.mm"
include "setsres.mm"
include "adantr.mm"
include "uneq1d.mm"
include "ovexd.mm"
include "setsval.mm"
include "sylan.mm"
include "3eqtr4d.mm"

theorem setsabs
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cV: class V
  let cW: class W


  assert |- ( ( S e. V /\ C e. W ) -> ( ( S sSet <. A , B >. ) sSet <. A , C >. ) = ( S sSet <. A , C >. ) )

  proof
    cS
    cV
    wcel
    #
    cC
    cW
    wcel
    #
    wa
    #
    cS
    cA
    cB
    cop
    #
    csts
    co
    #
    cvv
    cA
    csn
    cdif
    #
    cres
    #
    cA
    cC
    cop
    #
    csn
    #
    cun
    #
    cS
    @5
    cres
    #
    @8
    cun
    @4
    @7
    csts
    co
    #
    cS
    @7
    csts
    co
    @2
    @6
    @10
    @8
    @0
    @6
    @10
    wceq
    @1
    cA
    cB
    cS
    cV
    setsres
    adantr
    uneq1d
    @0
    @4
    cvv
    wcel
    @1
    @11
    @9
    wceq
    @0
    cS
    @3
    csts
    ovexd
    cA
    cC
    @4
    cvv
    cW
    setsval
    sylan
    cA
    cC
    cS
    cV
    cW
    setsval
    3eqtr4d
end
