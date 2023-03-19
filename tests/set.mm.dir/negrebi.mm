include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "cr.mm"
include "wb.mm"
include "negreb.mm"
include "ax-mp.mm"

theorem negrebi
  let cA: class A
  assume negidi.1: |- A e. CC


  assert |- ( -u A e. RR <-> A e. RR )

  proof
    cA
    cc
    wcel
    cA
    cneg
    cr
    wcel
    cA
    cr
    wcel
    wb
    negidi.1
    cA
    negreb
    ax-mp
end
