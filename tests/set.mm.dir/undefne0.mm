include "wcel.mm"
include "cund.mm"
include "cfv.mm"
include "cuni.mm"
include "cpw.mm"
include "c0.mm"
include "undefval.mm"
include "wne.mm"
include "pwne0.mm"
include "a1i.mm"
include "eqnetrd.mm"

theorem undefne0
  let cS: class S
  let cV: class V


  assert |- ( S e. V -> ( Undef ` S ) =/= (/) )

  proof
    cS
    cV
    wcel
    #
    cS
    cund
    cfv
    cS
    cuni
    #
    cpw
    #
    c0
    cS
    cV
    undefval
    @2
    c0
    wne
    @0
    @1
    pwne0
    a1i
    eqnetrd
end
