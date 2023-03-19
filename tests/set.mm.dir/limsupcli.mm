include "wcel.mm"
include "clsp.mm"
include "cfv.mm"
include "cxr.mm"
include "limsupcl.mm"
include "ax-mp.mm"

theorem limsupcli
  let cF: class F
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume limsupcli.1: |- F e. V


  assert |- ( limsup ` F ) e. RR*

  proof
    cF
    cV
    wcel
    cF
    clsp
    cfv
    cxr
    wcel
    limsupcli.1
    cF
    cV
    limsupcl
    ax-mp
end
