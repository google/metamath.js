include "cv.mm"
include "wcel.mm"
include "wf1o.mm"
include "cpmtr.mm"
include "cfv.mm"
include "eqid.mm"
include "pmtrff1o.mm"
include "elsymgbas2.mm"
include "mpbird.mm"
include "ssriv.mm"

theorem symgtrf
  let cB: class B
  let cD: class D
  let cT: class T
  let cG: class G
  let vx: setvar x
  assume symgtrf.t: |- T = ran ( pmTrsp ` D )
  assume symgtrf.g: |- G = ( SymGrp ` D )
  assume symgtrf.b: |- B = ( Base ` G )


  assert |- T C_ B

  proof
    vx
    cT
    cB
    vx
    cv
    #
    cT
    wcel
    @0
    cB
    wcel
    cD
    cD
    @0
    wf1o
    cD
    cT
    cD
    cpmtr
    cfv
    #
    @0
    @1
    eqid
    symgtrf.t
    pmtrff1o
    cD
    cB
    @0
    cG
    cT
    symgtrf.g
    symgtrf.b
    elsymgbas2
    mpbird
    ssriv
end
