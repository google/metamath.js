include "wcel.mm"
include "cund.mm"
include "cfv.mm"
include "cuni.mm"
include "cpw.mm"
include "pwuninel.mm"
include "undefval.mm"
include "eleq1d.mm"
include "mtbiri.mm"

theorem undefnel2
  let cS: class S
  let cV: class V


  assert |- ( S e. V -> -. ( Undef ` S ) e. S )

  proof
    cS
    cV
    wcel
    #
    cS
    cund
    cfv
    #
    cS
    wcel
    cS
    cuni
    cpw
    #
    cS
    wcel
    cS
    pwuninel
    @0
    @1
    @2
    cS
    cS
    cV
    undefval
    eleq1d
    mtbiri
end
