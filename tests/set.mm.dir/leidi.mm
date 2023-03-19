include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "leid.mm"
include "ax-mp.mm"

theorem leidi
  let cA: class A
  assume lt2.1: |- A e. RR


  assert |- A <_ A

  proof
    cA
    cr
    wcel
    cA
    cA
    cle
    wbr
    lt2.1
    cA
    leid
    ax-mp
end
