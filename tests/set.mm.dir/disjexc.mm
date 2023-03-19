include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wceq.mm"
include "wi.mm"
include "cin.mm"
include "c0.mm"
include "wo.mm"
include "imim2i.mm"
include "wn.mm"
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
include "3bitr4i.mm"
include "sylibr.mm"

theorem disjexc
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  assume disjexc.1: |- ( x = y -> A = B )

  disjoint A z
  disjoint B z
  assert |- ( ( E. z ( z e. A /\ z e. B ) -> x = y ) -> ( A = B \/ ( A i^i B ) = (/) ) )

  proof
    vz
    cv
    #
    cA
    wcel
    @0
    cB
    wcel
    wa
    #
    vz
    wex
    #
    vx
    cv
    vy
    cv
    wceq
    #
    wi
    @2
    cA
    cB
    wceq
    #
    wi
    #
    @4
    cA
    cB
    cin
    #
    c0
    wceq
    #
    wo
    #
    @3
    @4
    @2
    disjexc.1
    imim2i
    @4
    @2
    wn
    #
    wo
    @9
    @4
    wo
    @8
    @5
    @4
    @9
    orcom
    @7
    @9
    @4
    @2
    @6
    c0
    @6
    c0
    wne
    @1
    vz
    cab
    #
    c0
    wne
    @2
    @6
    @10
    c0
    vz
    cA
    cB
    df-in
    neeq1i
    @1
    vz
    abn0
    bitr2i
    necon2bbii
    orbi2i
    @2
    @4
    imor
    3bitr4i
    sylibr
end
