include "wcel.mm"
include "ctg.mm"
include "cfv.mm"
include "cv.mm"
include "cpw.mm"
include "cin.mm"
include "cuni.mm"
include "wss.mm"
include "wa.mm"
include "simpr.mm"
include "vex.mm"
include "pwid.mm"
include "a1i.mm"
include "elind.mm"
include "elssuni.mm"
include "syl.mm"
include "ex.mm"
include "eltg.mm"
include "sylibrd.mm"
include "ssrdv.mm"

theorem bastg
  let cB: class B
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cJ: class J
  let cC: class C


  assert |- ( B e. V -> B C_ ( topGen ` B ) )

  proof
    cB
    cV
    wcel
    #
    vx
    cB
    cB
    ctg
    cfv
    #
    @0
    vx
    cv
    #
    cB
    wcel
    #
    @2
    cB
    @2
    cpw
    #
    cin
    #
    cuni
    wss
    #
    @2
    @1
    wcel
    @0
    @3
    @6
    @0
    @3
    wa
    #
    @2
    @5
    wcel
    @6
    @7
    cB
    @4
    @2
    @0
    @3
    simpr
    @2
    @4
    wcel
    @7
    @2
    vx
    vex
    pwid
    a1i
    elind
    @2
    @5
    elssuni
    syl
    ex
    @2
    cB
    cV
    eltg
    sylibrd
    ssrdv
end
