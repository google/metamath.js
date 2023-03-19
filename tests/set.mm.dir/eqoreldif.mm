include "wcel.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "simpl.mm"
include "elsni.mm"
include "con3i.mm"
include "adantl.mm"
include "eldifd.mm"
include "ex.mm"
include "orrd.mm"
include "eleq1a.mm"
include "wi.mm"
include "eldifi.mm"
include "a1i.mm"
include "jaod.mm"
include "impbid2.mm"

theorem eqoreldif
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( B e. C -> ( A e. C <-> ( A = B \/ A e. ( C \ { B } ) ) ) )

  proof
    cB
    cC
    wcel
    #
    cA
    cC
    wcel
    #
    cA
    cB
    wceq
    #
    cA
    cC
    cB
    csn
    #
    cdif
    wcel
    #
    wo
    @1
    @2
    @4
    @1
    @2
    wn
    #
    @4
    @1
    @5
    wa
    cA
    cC
    @3
    @1
    @5
    simpl
    @5
    cA
    @3
    wcel
    #
    wn
    @1
    @6
    @2
    cA
    cB
    elsni
    con3i
    adantl
    eldifd
    ex
    orrd
    @0
    @2
    @1
    @4
    cB
    cC
    cA
    eleq1a
    @4
    @1
    wi
    @0
    cA
    cC
    @3
    eldifi
    a1i
    jaod
    impbid2
end
