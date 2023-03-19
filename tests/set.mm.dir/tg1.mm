include "ctg.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "cuni.mm"
include "wss.mm"
include "elfvdm.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "eltg2.mm"
include "simprbda.mm"
include "mpancom.mm"

theorem tg1
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cJ: class J
  let cV: class V
  let cC: class C


  assert |- ( A e. ( topGen ` B ) -> A C_ U. B )

  proof
    cB
    ctg
    cdm
    #
    wcel
    #
    cA
    cB
    ctg
    cfv
    wcel
    #
    cA
    cB
    cuni
    wss
    #
    cA
    cB
    ctg
    elfvdm
    @1
    @2
    @3
    vx
    cv
    vy
    cv
    #
    wcel
    @4
    cA
    wss
    wa
    vy
    cB
    wrex
    vx
    cA
    wral
    vx
    vy
    cA
    cB
    @0
    eltg2
    simprbda
    mpancom
end
