include "cperf.mm"
include "wcel.mm"
include "ctop.mm"
include "cuni.mm"
include "clp.mm"
include "cfv.mm"
include "wceq.mm"
include "eqid.mm"
include "isperf.mm"
include "simplbi.mm"

theorem perftop
  let cJ: class J


  assert |- ( J e. Perf -> J e. Top )

  proof
    cJ
    cperf
    wcel
    cJ
    ctop
    wcel
    cJ
    cuni
    #
    cJ
    clp
    cfv
    cfv
    @0
    wceq
    cJ
    @0
    @0
    eqid
    isperf
    simplbi
end
