include "chlo.mm"
include "wcel.mm"
include "ccbn.mm"
include "ccphlo.mm"
include "cnbn.mm"
include "cncph.mm"
include "ishlo.mm"
include "mpbir2an.mm"

theorem cnchl
  let cU: class U
  assume cnhl.6: |- U = <. <. + , x. >. , abs >.


  assert |- U e. CHilOLD

  proof
    cU
    chlo
    wcel
    cU
    ccbn
    wcel
    cU
    ccphlo
    wcel
    cU
    cnhl.6
    cnbn
    cU
    cnhl.6
    cncph
    cU
    ishlo
    mpbir2an
end
