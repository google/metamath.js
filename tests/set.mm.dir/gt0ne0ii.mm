include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wne.mm"
include "gt0ne0i.mm"
include "ax-mp.mm"

theorem gt0ne0ii
  let cA: class A
  assume lt2.1: |- A e. RR
  assume gt0ne0i.2: |- 0 < A


  assert |- A =/= 0

  proof
    cc0
    cA
    clt
    wbr
    cA
    cc0
    wne
    gt0ne0i.2
    cA
    lt2.1
    gt0ne0i
    ax-mp
end
