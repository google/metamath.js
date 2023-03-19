include "ctop.mm"
include "wcel.mm"
include "cnei.mm"
include "cfv.mm"
include "wa.mm"
include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "neii2.mm"
include "sstr.mm"
include "rexlimivw.mm"
include "syl.mm"

theorem ssnei
  let cS: class S
  let cJ: class J
  let cN: class N
  let vg: setvar g
  let cR: class R


  assert |- ( ( J e. Top /\ N e. ( ( nei ` J ) ` S ) ) -> S C_ N )

  proof
    cJ
    ctop
    wcel
    cN
    cS
    cJ
    cnei
    cfv
    cfv
    wcel
    wa
    cS
    vg
    cv
    #
    wss
    @0
    cN
    wss
    wa
    #
    vg
    cJ
    wrex
    cS
    cN
    wss
    #
    cS
    vg
    cJ
    cN
    neii2
    @1
    @2
    vg
    cJ
    cS
    @0
    cN
    sstr
    rexlimivw
    syl
end
