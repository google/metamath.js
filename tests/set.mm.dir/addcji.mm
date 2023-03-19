include "cc.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cre.mm"
include "cmul.mm"
include "wceq.mm"
include "addcj.mm"
include "ax-mp.mm"

theorem addcji
  let cA: class A
  assume recl.1: |- A e. CC


  assert |- ( A + ( * ` A ) ) = ( 2 x. ( Re ` A ) )

  proof
    cA
    cc
    wcel
    cA
    cA
    ccj
    cfv
    caddc
    co
    c2
    cA
    cre
    cfv
    cmul
    co
    wceq
    recl.1
    cA
    addcj
    ax-mp
end
