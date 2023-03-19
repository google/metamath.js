include "cvv.mm"
include "wcel.mm"
include "ctpos.mm"
include "tposexg.mm"
include "ax-mp.mm"

theorem tposex
  let cF: class F
  assume tposex.1: |- F e. _V


  assert |- tpos F e. _V

  proof
    cF
    cvv
    wcel
    cF
    ctpos
    cvv
    wcel
    tposex.1
    cF
    cvv
    tposexg
    ax-mp
end
