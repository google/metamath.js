include "hhnv.mm"
include "hhba.mm"
include "h2hvs.mm"

theorem hhvs
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  assume hhnv.1: |- U = <. <. +h , .h >. , normh >.


  assert |- -h = ( -v ` U )

  proof
    cU
    hhnv.1
    cU
    hhnv.1
    hhnv
    cU
    hhnv.1
    hhba
    h2hvs
end
