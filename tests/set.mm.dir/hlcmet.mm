include "chlo.mm"
include "wcel.mm"
include "ccbn.mm"
include "cms.mm"
include "cfv.mm"
include "hlobn.mm"
include "cbncms.mm"
include "syl.mm"

theorem hlcmet
  let cD: class D
  let cU: class U
  let cX: class X
  assume hlcmet.x: |- X = ( BaseSet ` U )
  assume hlcmet.8: |- D = ( IndMet ` U )


  assert |- ( U e. CHilOLD -> D e. ( CMet ` X ) )

  proof
    cU
    chlo
    wcel
    cU
    ccbn
    wcel
    cD
    cX
    cms
    cfv
    wcel
    cU
    hlobn
    cD
    cU
    cX
    hlcmet.x
    hlcmet.8
    cbncms
    syl
end
