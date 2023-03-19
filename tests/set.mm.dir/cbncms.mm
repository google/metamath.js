include "ccbn.mm"
include "wcel.mm"
include "cnv.mm"
include "cms.mm"
include "cfv.mm"
include "iscbn.mm"
include "simprbi.mm"

theorem cbncms
  let cD: class D
  let cU: class U
  let cX: class X
  let vu: setvar u
  assume iscbn.x: |- X = ( BaseSet ` U )
  assume iscbn.8: |- D = ( IndMet ` U )


  assert |- ( U e. CBan -> D e. ( CMet ` X ) )

  proof
    cU
    ccbn
    wcel
    cU
    cnv
    wcel
    cD
    cX
    cms
    cfv
    wcel
    cD
    cU
    cX
    iscbn.x
    iscbn.8
    iscbn
    simprbi
end
