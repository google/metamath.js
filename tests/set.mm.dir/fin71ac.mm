include "wac.mm"
include "cfin7.mm"
include "cfn.mm"
include "wceq.mm"
include "axac3.mm"
include "dfacfin7.mm"
include "mpbi.mm"

theorem fin71ac



  assert |- Fin7 = Fin

  proof
    wac
    cfin7
    cfn
    wceq
    axac3
    dfacfin7
    mpbi
end
