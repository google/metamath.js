include "ctop.mm"
include "wcel.mm"
include "ctg.mm"
include "cfv.mm"
include "cpw.mm"
include "cin.mm"
include "cuni.mm"
include "wss.mm"
include "tgtop.mm"
include "eleq2d.mm"
include "eltg.mm"
include "bitr3d.mm"

theorem eltop
  let cA: class A
  let cJ: class J
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cB: class B
  let cV: class V
  let cC: class C


  assert |- ( J e. Top -> ( A e. J <-> A C_ U. ( J i^i ~P A ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cJ
    ctg
    cfv
    #
    wcel
    cA
    cJ
    wcel
    cA
    cJ
    cA
    cpw
    cin
    cuni
    wss
    @0
    @1
    cJ
    cA
    cJ
    tgtop
    eleq2d
    cA
    cJ
    ctop
    eltg
    bitr3d
end
