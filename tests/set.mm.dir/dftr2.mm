include "cuni.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wtr.mm"
include "wa.mm"
include "dfss2.mm"
include "df-tr.mm"
include "wex.mm"
include "19.23v.mm"
include "eluni.mm"
include "imbi1i.mm"
include "bitr4i.mm"
include "albii.mm"
include "3bitr4i.mm"

theorem dftr2
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( Tr A <-> A. x A. y ( ( x e. y /\ y e. A ) -> x e. A ) )

  proof
    cA
    cuni
    #
    cA
    wss
    vx
    cv
    #
    @0
    wcel
    #
    @1
    cA
    wcel
    #
    wi
    #
    vx
    wal
    cA
    wtr
    @1
    vy
    cv
    #
    wcel
    @5
    cA
    wcel
    wa
    #
    @3
    wi
    vy
    wal
    #
    vx
    wal
    vx
    @0
    cA
    dfss2
    cA
    df-tr
    @7
    @4
    vx
    @7
    @6
    vy
    wex
    #
    @3
    wi
    @4
    @6
    @3
    vy
    19.23v
    @2
    @8
    @3
    vy
    @1
    cA
    eluni
    imbi1i
    bitr4i
    albii
    3bitr4i
end
