include "chil.mm"
include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cxmt.mm"
include "hhmet.mm"
include "metxmet.mm"
include "ax-mp.mm"

theorem hhxmet
  let cD: class D
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  assume hhnv.1: |- U = <. <. +h , .h >. , normh >.
  assume hhims2.2: |- D = ( IndMet ` U )


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
    cU
    hhnv.1
    hhims2.2
    hhmet
    cD
    chil
    metxmet
    ax-mp
end
