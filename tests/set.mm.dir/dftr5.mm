include "wtr.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "dftr2.mm"
include "alcom.mm"
include "impexp.mm"
include "albii.mm"
include "df-ral.mm"
include "bitr4i.mm"
include "r19.21v.mm"
include "bitri.mm"

theorem dftr5
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( Tr A <-> A. x e. A A. y e. x y e. A )

  proof
    cA
    wtr
    vy
    cv
    #
    vx
    cv
    #
    wcel
    #
    @1
    cA
    wcel
    #
    wa
    @0
    cA
    wcel
    #
    wi
    #
    vx
    wal
    vy
    wal
    #
    @4
    vy
    @1
    wral
    #
    vx
    cA
    wral
    #
    vy
    vx
    cA
    dftr2
    @6
    @5
    vy
    wal
    #
    vx
    wal
    #
    @8
    @5
    vy
    vx
    alcom
    @10
    @3
    @7
    wi
    #
    vx
    wal
    @8
    @9
    @11
    vx
    @9
    @3
    @4
    wi
    #
    vy
    @1
    wral
    #
    @11
    @9
    @2
    @12
    wi
    #
    vy
    wal
    @13
    @5
    @14
    vy
    @2
    @3
    @4
    impexp
    albii
    @12
    vy
    @1
    df-ral
    bitr4i
    @3
    @4
    vy
    @1
    r19.21v
    bitri
    albii
    @7
    vx
    cA
    df-ral
    bitr4i
    bitri
    bitri
end
