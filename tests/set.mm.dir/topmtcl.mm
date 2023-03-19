include "wcel.mm"
include "ctopon.mm"
include "cfv.mm"
include "cpw.mm"
include "cmre.mm"
include "wss.mm"
include "cint.mm"
include "cin.mm"
include "toponmre.mm"
include "mrerintcl.mm"
include "sylan.mm"

theorem topmtcl
  let cS: class S
  let cV: class V
  let cX: class X
  let vt: setvar t
  let vy: setvar y
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let cT: class T


  assert |- ( ( X e. V /\ S C_ ( TopOn ` X ) ) -> ( ~P X i^i |^| S ) e. ( TopOn ` X ) )

  proof
    cX
    cV
    wcel
    cX
    ctopon
    cfv
    #
    cX
    cpw
    #
    cmre
    cfv
    wcel
    cS
    @0
    wss
    @1
    cS
    cint
    cin
    @0
    wcel
    cX
    cV
    toponmre
    @0
    cS
    @1
    mrerintcl
    sylan
end
