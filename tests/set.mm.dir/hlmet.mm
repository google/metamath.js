include "chlo.mm"
include "wcel.mm"
include "cms.mm"
include "cfv.mm"
include "cme.mm"
include "hlcmet.mm"
include "cmetmet.mm"
include "syl.mm"

theorem hlmet
  let cD: class D
  let cU: class U
  let cX: class X
  assume hlcmet.x: |- X = ( BaseSet ` U )
  assume hlcmet.8: |- D = ( IndMet ` U )


  assert |- ( U e. CHilOLD -> D e. ( Met ` X ) )

  proof
    cU
    chlo
    wcel
    cD
    cX
    cms
    cfv
    wcel
    cD
    cX
    cme
    cfv
    wcel
    cD
    cU
    cX
    hlcmet.x
    hlcmet.8
    hlcmet
    cD
    cX
    cmetmet
    syl
end
