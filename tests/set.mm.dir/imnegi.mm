include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "cim.mm"
include "cfv.mm"
include "wceq.mm"
include "imneg.mm"
include "ax-mp.mm"

theorem imnegi
  let cA: class A
  assume recl.1: |- A e. CC


  assert |- ( Im ` -u A ) = -u ( Im ` A )

  proof
    cA
    cc
    wcel
    cA
    cneg
    cim
    cfv
    cA
    cim
    cfv
    cneg
    wceq
    recl.1
    cA
    imneg
    ax-mp
end
