include "cc.mm"
include "cnfldtopon.mm"
include "topontopi.mm"

theorem cnfldtop
  let cJ: class J
  assume cnfldtopn.1: |- J = ( TopOpen ` CCfld )


  assert |- J e. Top

  proof
    cc
    cJ
    cJ
    cnfldtopn.1
    cnfldtopon
    topontopi
end
