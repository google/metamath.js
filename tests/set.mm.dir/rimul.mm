include "cr.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "wa.mm"
include "wn.mm"
include "cc0.mm"
include "wceq.mm"
include "inelr.mm"
include "wne.mm"
include "cdiv.mm"
include "cc.mm"
include "ax-icn.mm"
include "a1i.mm"
include "simpll.mm"
include "recnd.mm"
include "simpr.mm"
include "divcan4d.mm"
include "simplr.mm"
include "redivcld.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "necon1bd.mm"
include "mpi.mm"

theorem rimul
  let cA: class A


  assert |- ( ( A e. RR /\ ( _i x. A ) e. RR ) -> A = 0 )

  proof
    cA
    cr
    wcel
    #
    ci
    cA
    cmul
    co
    #
    cr
    wcel
    #
    wa
    #
    ci
    cr
    wcel
    #
    wn
    cA
    cc0
    wceq
    inelr
    @3
    @4
    cA
    cc0
    @3
    cA
    cc0
    wne
    #
    @4
    @3
    @5
    wa
    #
    @1
    cA
    cdiv
    co
    ci
    cr
    @6
    ci
    cA
    ci
    cc
    wcel
    @6
    ax-icn
    a1i
    @6
    cA
    @0
    @2
    @5
    simpll
    #
    recnd
    @3
    @5
    simpr
    #
    divcan4d
    @6
    @1
    cA
    @0
    @2
    @5
    simplr
    @7
    @8
    redivcld
    eqeltrrd
    ex
    necon1bd
    mpi
end
