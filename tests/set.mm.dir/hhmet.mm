include "cnv.mm"
include "wcel.mm"
include "chil.mm"
include "cme.mm"
include "cfv.mm"
include "hhnv.mm"
include "hhba.mm"
include "imsmet.mm"
include "ax-mp.mm"

theorem hhmet
  let cD: class D
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  assume hhnv.1: |- U = <. <. +h , .h >. , normh >.
  assume hhims2.2: |- D = ( IndMet ` U )


  assert |- D e. ( Met ` ~H )

  proof
    cU
    cnv
    wcel
    cD
    chil
    cme
    cfv
    wcel
    cU
    hhnv.1
    hhnv
    cD
    cU
    chil
    cU
    hhnv.1
    hhba
    hhims2.2
    imsmet
    ax-mp
end
