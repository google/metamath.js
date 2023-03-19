include "hhnv.mm"
include "hhba.mm"
include "h2hcau.mm"

theorem hhcau
  let cD: class D
  let cU: class U
  assume hhlm.1: |- U = <. <. +h , .h >. , normh >.
  assume hhlm.2: |- D = ( IndMet ` U )


  assert |- Cauchy = ( ( Cau ` D ) i^i ( ~H ^m NN ) )

  proof
    cD
    cU
    hhlm.1
    cU
    hhlm.1
    hhnv
    cU
    hhlm.1
    hhba
    hhlm.2
    h2hcau
end
