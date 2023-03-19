include "cgru.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cpw.mm"
include "wb.mm"
include "elpw2g.mm"
include "adantl.mm"
include "grupw.mm"
include "gruelss.mm"
include "syldan.mm"
include "sseld.mm"
include "sylbird.mm"
include "3impia.mm"

theorem gruss
  let cA: class A
  let cB: class B
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let cF: class F


  assert |- ( ( U e. Univ /\ A e. U /\ B C_ A ) -> B e. U )

  proof
    cU
    cgru
    wcel
    #
    cA
    cU
    wcel
    #
    cB
    cA
    wss
    #
    cB
    cU
    wcel
    #
    @0
    @1
    wa
    #
    @2
    cB
    cA
    cpw
    #
    wcel
    #
    @3
    @1
    @6
    @2
    wb
    @0
    cB
    cA
    cU
    elpw2g
    adantl
    @4
    @5
    cU
    cB
    @0
    @1
    @5
    cU
    wcel
    @5
    cU
    wss
    cA
    cU
    grupw
    @5
    cU
    gruelss
    syldan
    sseld
    sylbird
    3impia
end
