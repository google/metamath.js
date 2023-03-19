include "chil.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "chssii.mm"
include "ssjo.mm"
include "ax-mp.mm"

theorem chjoi
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  assume ch0le.1: |- A e. CH


  assert |- ( A vH ( _|_ ` A ) ) = ~H

  proof
    cA
    chil
    wss
    cA
    cA
    cort
    cfv
    chj
    co
    chil
    wceq
    cA
    ch0le.1
    chssii
    cA
    ssjo
    ax-mp
end
