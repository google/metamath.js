include "cc.mm"
include "wcel.mm"
include "cim.mm"
include "cfv.mm"
include "cr.mm"
include "imcl.mm"
include "ax-mp.mm"

theorem imcli
  let cA: class A
  assume recl.1: |- A e. CC


  assert |- ( Im ` A ) e. RR

  proof
    cA
    cc
    wcel
    cA
    cim
    cfv
    cr
    wcel
    recl.1
    cA
    imcl
    ax-mp
end
