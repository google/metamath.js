include "hhnv.mm"
include "hhba.mm"
include "h2hlm.mm"

theorem hhlm
  let cD: class D
  let cU: class U
  let cJ: class J
  assume hhlm.1: |- U = <. <. +h , .h >. , normh >.
  assume hhlm.2: |- D = ( IndMet ` U )
  assume hhlm.3: |- J = ( MetOpen ` D )


  assert |- ~~>v = ( ( ~~>t ` J ) |` ( ~H ^m NN ) )

  proof
    cD
    cU
    cJ
    hhlm.1
    cU
    hhlm.1
    hhnv
    cU
    hhlm.1
    hhba
    hhlm.2
    hhlm.3
    h2hlm
end
