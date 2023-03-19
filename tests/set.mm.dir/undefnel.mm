include "wcel.mm"
include "cund.mm"
include "cfv.mm"
include "wn.mm"
include "wnel.mm"
include "undefnel2.mm"
include "df-nel.mm"
include "sylibr.mm"

theorem undefnel
  let cS: class S
  let cV: class V


  assert |- ( S e. V -> ( Undef ` S ) e/ S )

  proof
    cS
    cV
    wcel
    cS
    cund
    cfv
    #
    cS
    wcel
    wn
    @0
    cS
    wnel
    cS
    cV
    undefnel2
    @0
    cS
    df-nel
    sylibr
end
