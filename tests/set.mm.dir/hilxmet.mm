include "chil.mm"
include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cxmt.mm"
include "hilmet.mm"
include "metxmet.mm"
include "ax-mp.mm"

theorem hilxmet
  let cD: class D
  assume hilmet.1: |- D = ( normh o. -h )


  assert |- D e. ( *Met ` ~H )

  proof
    cD
    chil
    cme
    cfv
    wcel
    cD
    chil
    cxmt
    cfv
    wcel
    cD
    hilmet.1
    hilmet
    cD
    chil
    metxmet
    ax-mp
end
