include "hilhhi.mm"
include "hhims2.mm"

theorem hilims
  let cD: class D
  let cU: class U
  assume hilims.1: |- ~H = ( BaseSet ` U )
  assume hilims.2: |- +h = ( +v ` U )
  assume hilims.3: |- .h = ( .sOLD ` U )
  assume hilims.5: |- .ih = ( .iOLD ` U )
  assume hilims.8: |- D = ( IndMet ` U )
  assume hilims.9: |- U e. NrmCVec


  assert |- D = ( normh o. -h )

  proof
    cD
    cU
    cU
    hilims.1
    hilims.2
    hilims.3
    hilims.5
    hilims.9
    hilhhi
    hilims.8
    hhims2
end
