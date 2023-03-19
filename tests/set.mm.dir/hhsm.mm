include "hhnv.mm"
include "h2hsm.mm"

theorem hhsm
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  assume hhnv.1: |- U = <. <. +h , .h >. , normh >.


  assert |- .h = ( .sOLD ` U )

  proof
    cU
    hhnv.1
    cU
    hhnv.1
    hhnv
    h2hsm
end
