include "clf.mm"
include "wcel.mm"
include "chil.mm"
include "cc.mm"
include "wf.mm"
include "lnfnf.mm"
include "ax-mp.mm"

theorem lnfnfi
  let cT: class T
  assume lnfnl.1: |- T e. LinFn


  assert |- T : ~H --> CC

  proof
    cT
    clf
    wcel
    chil
    cc
    cT
    wf
    lnfnl.1
    cT
    lnfnf
    ax-mp
end
