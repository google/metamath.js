include "cnv.mm"
include "wcel.mm"
include "cme.mm"
include "cfv.mm"
include "cxmt.mm"
include "imsmet.mm"
include "metxmet.mm"
include "syl.mm"

theorem imsxmet
  let cD: class D
  let cU: class U
  let cX: class X
  assume imsmet.1: |- X = ( BaseSet ` U )
  assume imsmet.8: |- D = ( IndMet ` U )


  assert |- ( U e. NrmCVec -> D e. ( *Met ` X ) )

  proof
    cU
    cnv
    wcel
    cD
    cX
    cme
    cfv
    wcel
    cD
    cX
    cxmt
    cfv
    wcel
    cD
    cU
    cX
    imsmet.1
    imsmet.8
    imsmet
    cD
    cX
    metxmet
    syl
end
