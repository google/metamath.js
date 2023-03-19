include "wcel.mm"
include "wss.mm"
include "cuni.mm"
include "cv.mm"
include "wi.mm"
include "wal.mm"
include "wceq.mm"
include "eleq2.mm"
include "imbi1d.mm"
include "elunii.mm"
include "expcom.mm"
include "vtoclga.mm"
include "imim2d.mm"
include "alimdv.mm"
include "dfss2.mm"
include "3imtr4g.mm"
include "impcom.mm"

theorem ssuniOLD
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
    @4
    vx
    cv
    #
    wcel
    #
    @8
    wi
    @6
    @8
    wi
    vx
    cB
    cC
    @10
    cB
    wceq
    @11
    @6
    @8
    @10
    cB
    @4
    eleq2
    imbi1d
    @11
    @10
    cC
    wcel
    @8
    @4
    @10
    cC
    elunii
    expcom
    vtoclga
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
