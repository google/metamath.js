include "cgru.mm"
include "wcel.mm"
include "w3a.mm"
include "cun.mm"
include "cxp.mm"
include "gruun.mm"
include "cpw.mm"
include "grupw.mm"
include "wss.mm"
include "xpsspw.mm"
include "gruss.mm"
include "mp3an3.mm"
include "syldan.mm"
include "3ad2antl1.mm"
include "mpdan.mm"

theorem gruxp
  let cA: class A
  let cB: class B
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let cF: class F


  assert |- ( ( U e. Univ /\ A e. U /\ B e. U ) -> ( A X. B ) e. U )

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
    cU
    wcel
    #
    w3a
    cA
    cB
    cun
    #
    cU
    wcel
    #
    cA
    cB
    cxp
    #
    cU
    wcel
    #
    cA
    cB
    cU
    gruun
    @0
    @1
    @4
    @6
    @2
    @0
    @4
    @3
    cpw
    #
    cU
    wcel
    #
    @6
    @3
    cU
    grupw
    @0
    @8
    @7
    cpw
    #
    cU
    wcel
    #
    @6
    @7
    cU
    grupw
    @0
    @10
    @5
    @9
    wss
    @6
    cA
    cB
    xpsspw
    @9
    @5
    cU
    gruss
    mp3an3
    syldan
    syldan
    3ad2antl1
    mpdan
end
