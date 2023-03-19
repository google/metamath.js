include "cvv.mm"
include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "w3a.mm"
include "ccom.mm"
include "elmapi.mm"
include "fco.mm"
include "sylan.mm"
include "3adant1.mm"
include "c0.mm"
include "wceq.mm"
include "n0i.mm"
include "reldmmap.mm"
include "ovprc1.mm"
include "nsyl2.mm"
include "3ad2ant2.mm"
include "simp1.mm"
include "elmapd.mm"
include "mpbird.mm"

theorem mapco2g
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E


  assert |- ( ( E e. _V /\ A e. ( B ^m C ) /\ D : E --> C ) -> ( A o. D ) e. ( B ^m E ) )

  proof
    cE
    cvv
    wcel
    #
    cA
    cB
    cC
    cmap
    co
    #
    wcel
    #
    cE
    cC
    cD
    wf
    #
    w3a
    #
    cA
    cD
    ccom
    #
    cB
    cE
    cmap
    co
    wcel
    cE
    cB
    @5
    wf
    #
    @2
    @3
    @6
    @0
    @2
    cC
    cB
    cA
    wf
    @3
    @6
    cA
    cB
    cC
    elmapi
    cE
    cC
    cB
    cA
    cD
    fco
    sylan
    3adant1
    @4
    cB
    cE
    @5
    cvv
    cvv
    @2
    @0
    cB
    cvv
    wcel
    #
    @3
    @2
    @1
    c0
    wceq
    @7
    @1
    cA
    n0i
    cB
    cC
    cmap
    reldmmap
    ovprc1
    nsyl2
    3ad2ant2
    @0
    @2
    @3
    simp1
    elmapd
    mpbird
end
