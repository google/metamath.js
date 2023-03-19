include "hhnv.mm"
include "h2hnm.mm"

theorem hhnm
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  assume hhnv.1: |- U = <. <. +h , .h >. , normh >.


  assert |- normh = ( normCV ` U )

  proof
    cU
    hhnv.1
    cU
    hhnv.1
    hhnv
    h2hnm
end
