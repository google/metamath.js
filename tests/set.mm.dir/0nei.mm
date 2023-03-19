include "ctop.mm"
include "wcel.mm"
include "c0.mm"
include "cnei.mm"
include "cfv.mm"
include "0opn.mm"
include "opnneiid.mm"
include "mpbird.mm"

theorem 0nei
  let cJ: class J


  assert |- ( J e. Top -> (/) e. ( ( nei ` J ) ` (/) ) )

  proof
    cJ
    ctop
    wcel
    c0
    c0
    cJ
    cnei
    cfv
    cfv
    wcel
    c0
    cJ
    wcel
    cJ
    0opn
    cJ
    c0
    opnneiid
    mpbird
end
