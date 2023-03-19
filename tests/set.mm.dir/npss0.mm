include "c0.mm"
include "wss.mm"
include "wpss.mm"
include "wn.mm"
include "0ss.mm"
include "ssnpss.mm"
include "ax-mp.mm"

theorem npss0
  let cA: class A


  assert |- -. A C. (/)

  proof
    c0
    cA
    wss
    cA
    c0
    wpss
    wn
    cA
    0ss
    c0
    cA
    ssnpss
    ax-mp
end
