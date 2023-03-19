include "cv.mm"
include "wceq.mm"
include "cin.mm"
include "c0.mm"
include "wo.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wn.mm"
include "orcom.mm"
include "df-or.mm"
include "wex.mm"
include "neq0.mm"
include "elin.mm"
include "exbii.mm"
include "bitri.mm"
include "imbi1i.mm"
include "19.23v.mm"
include "bitr4i.mm"
include "3bitri.mm"
include "ralbii.mm"
include "ralcom4.mm"

theorem ineleq
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D

  disjoint B z
  disjoint C z
  disjoint D z
  disjoint x z
  disjoint y z
  assert |- ( A. x e. A A. y e. B ( x = y \/ ( C i^i D ) = (/) ) <-> A. x e. A A. z A. y e. B ( ( z e. C /\ z e. D ) -> x = y ) )

  proof
    vx
    cv
    vy
    cv
    wceq
    #
    cC
    cD
    cin
    #
    c0
    wceq
    #
    wo
    #
    vy
    cB
    wral
    #
    vz
    cv
    #
    cC
    wcel
    @5
    cD
    wcel
    wa
    #
    @0
    wi
    #
    vy
    cB
    wral
    vz
    wal
    #
    vx
    cA
    @4
    @7
    vz
    wal
    #
    vy
    cB
    wral
    @8
    @3
    @9
    vy
    cB
    @3
    @2
    @0
    wo
    @2
    wn
    #
    @0
    wi
    #
    @9
    @0
    @2
    orcom
    @2
    @0
    df-or
    @11
    @6
    vz
    wex
    #
    @0
    wi
    @9
    @10
    @12
    @0
    @10
    @5
    @1
    wcel
    #
    vz
    wex
    @12
    vz
    @1
    neq0
    @13
    @6
    vz
    @5
    cC
    cD
    elin
    exbii
    bitri
    imbi1i
    @6
    @0
    vz
    19.23v
    bitr4i
    3bitri
    ralbii
    @7
    vy
    vz
    cB
    ralcom4
    bitri
    ralbii
end
