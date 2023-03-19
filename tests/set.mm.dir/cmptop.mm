include "ccmp.mm"
include "wcel.mm"
include "ctop.mm"
include "cuni.mm"
include "cv.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "eqid.mm"
include "iscmp.mm"
include "simplbi.mm"

theorem cmptop
  let cJ: class J
  let vr: setvar r
  let vs: setvar s


  assert |- ( J e. Comp -> J e. Top )

  proof
    cJ
    ccmp
    wcel
    cJ
    ctop
    wcel
    cJ
    cuni
    #
    vr
    cv
    #
    cuni
    wceq
    @0
    vs
    cv
    cuni
    wceq
    vs
    @1
    cpw
    cfn
    cin
    wrex
    wi
    vr
    cJ
    cpw
    wral
    vr
    vs
    cJ
    @0
    @0
    eqid
    iscmp
    simplbi
end
