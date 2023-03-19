include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wn.mm"
include "wo.mm"
include "cin.mm"
include "c0.mm"
include "wi.mm"
include "orcom.mm"
include "wne.mm"
include "cab.mm"
include "df-in.mm"
include "neeq1i.mm"
include "abn0.mm"
include "bitr2i.mm"
include "necon2bbii.mm"
include "orbi2i.mm"
include "imor.mm"
include "3bitr4ri.mm"

theorem disjex
  let vz: setvar z
  let cA: class A
  let cB: class B

  disjoint A z
  disjoint B z
  assert |- ( ( E. z ( z e. A /\ z e. B ) -> A = B ) <-> ( A = B \/ ( A i^i B ) = (/) ) )

  proof
    cA
    cB
    wceq
    #
    vz
    cv
    #
    cA
    wcel
    @1
    cB
    wcel
    wa
    #
    vz
    wex
    #
    wn
    #
    wo
    @4
    @0
    wo
    @0
    cA
    cB
    cin
    #
    c0
    wceq
    #
    wo
    @3
    @0
    wi
    @0
    @4
    orcom
    @6
    @4
    @0
    @3
    @5
    c0
    @5
    c0
    wne
    @2
    vz
    cab
    #
    c0
    wne
    @3
    @5
    @7
    c0
    vz
    cA
    cB
    df-in
    neeq1i
    @2
    vz
    abn0
    bitr2i
    necon2bbii
    orbi2i
    @3
    @0
    imor
    3bitr4ri
end
