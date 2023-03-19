include "cv.mm"
include "wcel.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "wmo.mm"
include "ralcom4.mm"
include "df-ral.mm"
include "ralbii.mm"
include "wa.mm"
include "alcom.mm"
include "eleq1.mm"
include "mo4.mm"
include "impexp.mm"
include "albii.mm"
include "bitr4i.mm"
include "3bitr4i.mm"
include "3bitr4ri.mm"

theorem moel
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( E* x x e. A <-> A. x e. A A. y e. A x = y )

  proof
    vy
    cv
    #
    cA
    wcel
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    wal
    #
    vx
    cA
    wral
    @3
    vx
    cA
    wral
    #
    vy
    wal
    #
    @2
    vy
    cA
    wral
    #
    vx
    cA
    wral
    vx
    cv
    #
    cA
    wcel
    #
    vx
    wmo
    #
    @3
    vx
    vy
    cA
    ralcom4
    @7
    @4
    vx
    cA
    @2
    vy
    cA
    df-ral
    ralbii
    @9
    @1
    wa
    @2
    wi
    #
    vy
    wal
    vx
    wal
    @11
    vx
    wal
    #
    vy
    wal
    @10
    @6
    @11
    vx
    vy
    alcom
    @9
    @1
    vx
    vy
    @8
    @0
    cA
    eleq1
    mo4
    @5
    @12
    vy
    @5
    @9
    @3
    wi
    #
    vx
    wal
    @12
    @3
    vx
    cA
    df-ral
    @11
    @13
    vx
    @9
    @1
    @2
    impexp
    albii
    bitr4i
    albii
    3bitr4i
    3bitr4ri
end
