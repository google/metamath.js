include "ctop.mm"
include "wcel.mm"
include "c0.mm"
include "cuni.mm"
include "uni0.mm"
include "wss.mm"
include "0ss.mm"
include "uniopn.mm"
include "mpan2.mm"
include "syl5eqelr.mm"

theorem 0opn
  let cJ: class J


  assert |- ( J e. Top -> (/) e. J )

  proof
    cJ
    ctop
    wcel
    #
    c0
    c0
    cuni
    #
    cJ
    uni0
    @0
    c0
    cJ
    wss
    @1
    cJ
    wcel
    cJ
    0ss
    c0
    cJ
    uniopn
    mpan2
    syl5eqelr
end
