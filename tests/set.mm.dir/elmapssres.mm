include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cres.mm"
include "wf.mm"
include "elmapi.mm"
include "fssres.mm"
include "sylan.mm"
include "cvv.mm"
include "elmapex.mm"
include "simpld.mm"
include "adantr.mm"
include "simprd.mm"
include "ssexg.mm"
include "ancoms.mm"
include "elmapd.mm"
include "mpbird.mm"

theorem elmapssres
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A e. ( B ^m C ) /\ D C_ C ) -> ( A |` D ) e. ( B ^m D ) )

  proof
    cA
    cB
    cC
    cmap
    co
    wcel
    #
    cD
    cC
    wss
    #
    wa
    #
    cA
    cD
    cres
    #
    cB
    cD
    cmap
    co
    wcel
    cD
    cB
    @3
    wf
    #
    @0
    cC
    cB
    cA
    wf
    @1
    @4
    cA
    cB
    cC
    elmapi
    cC
    cB
    cD
    cA
    fssres
    sylan
    @2
    cB
    cD
    @3
    cvv
    cvv
    @0
    cB
    cvv
    wcel
    #
    @1
    @0
    @5
    cC
    cvv
    wcel
    #
    cA
    cB
    cC
    elmapex
    #
    simpld
    adantr
    @0
    @6
    @1
    cD
    cvv
    wcel
    #
    @0
    @5
    @6
    @7
    simprd
    @1
    @6
    @8
    cD
    cC
    cvv
    ssexg
    ancoms
    sylan
    elmapd
    mpbird
end
