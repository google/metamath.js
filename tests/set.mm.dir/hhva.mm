include "hhnv.mm"
include "h2hva.mm"

theorem hhva
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  assume hhnv.1: |- U = <. <. +h , .h >. , normh >.


  assert |- +h = ( +v ` U )

  proof
    cU
    hhnv.1
    cU
    hhnv.1
    hhnv
    h2hva
end
