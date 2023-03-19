include "c0.mm"
include "wne.mm"
include "ciin.mm"
include "wceq.mm"
include "iinconst.mm"
include "cvv.mm"
include "0ex.mm"
include "n0ii.mm"
include "0iin.mm"
include "eqeq1i.mm"
include "mtbir.mm"
include "iineq1.mm"
include "eqeq1d.mm"
include "mtbiri.mm"
include "necon2ai.mm"
include "impbii.mm"

theorem iin0
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A =/= (/) <-> |^|_ x e. A (/) = (/) )

  proof
    cA
    c0
    wne
    vx
    cA
    c0
    ciin
    #
    c0
    wceq
    #
    vx
    cA
    c0
    iinconst
    @1
    cA
    c0
    cA
    c0
    wceq
    #
    @1
    vx
    c0
    c0
    ciin
    #
    c0
    wceq
    #
    @4
    cvv
    c0
    wceq
    c0
    cvv
    0ex
    n0ii
    @3
    cvv
    c0
    vx
    c0
    0iin
    eqeq1i
    mtbir
    @2
    @0
    @3
    c0
    vx
    cA
    c0
    c0
    iineq1
    eqeq1d
    mtbiri
    necon2ai
    impbii
end
