include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "cuni.mm"
include "csiga.mm"
include "cfv.mm"
include "crab.mm"
include "cint.mm"
include "csigagen.mm"
include "ssintub.mm"
include "sigagenval.mm"
include "syl5sseqr.mm"

theorem sssigagen
  let cA: class A
  let cV: class V
  let vs: setvar s


  assert |- ( A e. V -> A C_ ( sigaGen ` A ) )

  proof
    cA
    cV
    wcel
    cA
    vs
    cv
    wss
    vs
    cA
    cuni
    csiga
    cfv
    #
    crab
    cint
    cA
    cA
    csigagen
    cfv
    vs
    cA
    @0
    ssintub
    cA
    cV
    vs
    sigagenval
    syl5sseqr
end
