include "cuz.mm"
include "cfv.mm"
include "cc.mm"
include "uzsscn.mm"
include "eqsstri.mm"

theorem uzsscn2
  let cM: class M
  let cZ: class Z
  assume uzsscn2.1: |- Z = ( ZZ>= ` M )


  assert |- Z C_ CC

  proof
    cZ
    cM
    cuz
    cfv
    cc
    uzsscn2.1
    cM
    uzsscn
    eqsstri
end
