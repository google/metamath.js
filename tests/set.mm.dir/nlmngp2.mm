include "cnlm.mm"
include "wcel.mm"
include "cnrg.mm"
include "cngp.mm"
include "nlmnrg.mm"
include "nrgngp.mm"
include "syl.mm"

theorem nlmngp2
  let cF: class F
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume nlmnrg.1: |- F = ( Scalar ` W )


  assert |- ( W e. NrmMod -> F e. NrmGrp )

  proof
    cW
    cnlm
    wcel
    cF
    cnrg
    wcel
    cF
    cngp
    wcel
    cF
    cW
    nlmnrg.1
    nlmnrg
    cF
    nrgngp
    syl
end
