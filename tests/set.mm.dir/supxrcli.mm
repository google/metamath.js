include "cxr.mm"
include "wss.mm"
include "clt.mm"
include "csup.mm"
include "wcel.mm"
include "supxrcl.mm"
include "ax-mp.mm"

theorem supxrcli
  let cA: class A
  assume supxrcli.1: |- A C_ RR*


  assert |- sup ( A , RR* , < ) e. RR*

  proof
    cA
    cxr
    wss
    cA
    cxr
    clt
    csup
    cxr
    wcel
    supxrcli.1
    cA
    supxrcl
    ax-mp
end
