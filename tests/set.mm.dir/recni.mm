include "cr.mm"
include "cc.mm"
include "ax-resscn.mm"
include "sselii.mm"

theorem recni
  let cA: class A
  assume recni.1: |- A e. RR


  assert |- A e. CC

  proof
    cr
    cc
    cA
    ax-resscn
    recni.1
    sselii
end
