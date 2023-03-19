include "crp.mm"
include "wcel.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "clog.mm"
include "cfv.mm"
include "ce.mm"
include "wceq.mm"
include "rpcnne0.mm"
include "eflog.mm"
include "syl.mm"

theorem reeflog
  let cA: class A


  assert |- ( A e. RR+ -> ( exp ` ( log ` A ) ) = A )

  proof
    cA
    crp
    wcel
    cA
    cc
    wcel
    cA
    cc0
    wne
    wa
    cA
    clog
    cfv
    ce
    cfv
    cA
    wceq
    cA
    rpcnne0
    cA
    eflog
    syl
end
