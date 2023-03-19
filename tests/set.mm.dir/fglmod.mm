include "clfig.mm"
include "clmod.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "clspn.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cima.mm"
include "wcel.mm"
include "crab.mm"
include "df-lfig.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseli.mm"

theorem fglmod
  let cM: class M
  let va: setvar a


  assert |- ( M e. LFinGen -> M e. LMod )

  proof
    clfig
    clmod
    cM
    clfig
    va
    cv
    #
    cbs
    cfv
    #
    @0
    clspn
    cfv
    @1
    cpw
    cfn
    cin
    cima
    wcel
    #
    va
    clmod
    crab
    clmod
    va
    df-lfig
    @2
    va
    clmod
    ssrab2
    eqsstri
    sseli
end
