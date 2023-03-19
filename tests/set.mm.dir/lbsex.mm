include "wac.mm"
include "clvec.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "axac3.mm"
include "lbsexg.mm"
include "mpan.mm"

theorem lbsex
  let cJ: class J
  let cW: class W
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cN: class N
  let cV: class V
  assume lbsex.j: |- J = ( LBasis ` W )


  assert |- ( W e. LVec -> J =/= (/) )

  proof
    wac
    cW
    clvec
    wcel
    cJ
    c0
    wne
    axac3
    cJ
    cW
    lbsex.j
    lbsexg
    mpan
end
