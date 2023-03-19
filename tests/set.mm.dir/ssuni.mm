include "wcel.mm"
include "wss.mm"
include "cuni.mm"
include "cv.mm"
include "wi.mm"
include "wal.mm"
include "elunii.mm"
include "expcom.mm"
include "imim2d.mm"
include "alimdv.mm"
include "dfss2.mm"
include "3imtr4g.mm"
include "impcom.mm"

theorem ssuni
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A C_ B /\ B e. C ) -> A C_ U. C )

  proof
    cB
    cC
    wcel
    #
    cA
    cB
    wss
    #
    cA
    cC
    cuni
    #
    wss
    #
    @0
    vy
    cv
    #
    cA
    wcel
    #
    @4
    cB
    wcel
    #
    wi
    #
    vy
    wal
    @5
    @4
    @2
    wcel
    #
    wi
    #
    vy
    wal
    @1
    @3
    @0
    @7
    @9
    vy
    @0
    @6
    @8
    @5
    @6
    @0
    @8
    @4
    cB
    cC
    elunii
    expcom
    imim2d
    alimdv
    vy
    cA
    cB
    dfss2
    vy
    cA
    @2
    dfss2
    3imtr4g
    impcom
end
