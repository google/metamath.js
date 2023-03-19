include "cgru.mm"
include "wcel.mm"
include "wa.mm"
include "cuni.mm"
include "cv.mm"
include "ciun.mm"
include "uniiun.mm"
include "wral.mm"
include "wss.mm"
include "gruelss.mm"
include "dfss3.mm"
include "sylib.mm"
include "gruiun.mm"
include "mpd3an3.mm"
include "syl5eqel.mm"

theorem gruuni
  let cA: class A
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cF: class F


  assert |- ( ( U e. Univ /\ A e. U ) -> U. A e. U )

  proof
    cU
    cgru
    wcel
    #
    cA
    cU
    wcel
    #
    wa
    #
    cA
    cuni
    vx
    cA
    vx
    cv
    #
    ciun
    #
    cU
    vx
    cA
    uniiun
    @0
    @1
    @3
    cU
    wcel
    vx
    cA
    wral
    #
    @4
    cU
    wcel
    @2
    cA
    cU
    wss
    @5
    cA
    cU
    gruelss
    vx
    cA
    cU
    dfss3
    sylib
    vx
    cA
    @3
    cU
    gruiun
    mpd3an3
    syl5eqel
end
