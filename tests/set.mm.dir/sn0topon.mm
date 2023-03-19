include "c0.mm"
include "cpw.mm"
include "csn.mm"
include "ctopon.mm"
include "cfv.mm"
include "pw0.mm"
include "cvv.mm"
include "wcel.mm"
include "0ex.mm"
include "distopon.mm"
include "ax-mp.mm"
include "eqeltrri.mm"

theorem sn0topon
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cV: class V


  assert |- { (/) } e. ( TopOn ` (/) )

  proof
    c0
    cpw
    #
    c0
    csn
    c0
    ctopon
    cfv
    #
    pw0
    c0
    cvv
    wcel
    @0
    @1
    wcel
    0ex
    c0
    cvv
    distopon
    ax-mp
    eqeltrri
end
