include "ctop.mm"
include "wcel.mm"
include "ccl.mm"
include "cfv.mm"
include "cuni.mm"
include "cpw.mm"
include "cv.mm"
include "wss.mm"
include "ccld.mm"
include "crab.mm"
include "cint.mm"
include "cmpt.mm"
include "eqid.mm"
include "clsfval.mm"
include "cmre.mm"
include "wceq.mm"
include "cldmre.mm"
include "mrcfval.mm"
include "syl.mm"
include "eqtr4d.mm"

theorem mrccls
  let cF: class F
  let cJ: class J
  let va: setvar a
  let vb: setvar b
  assume mrccls.f: |- F = ( mrCls ` ( Clsd ` J ) )


  assert |- ( J e. Top -> ( cls ` J ) = F )

  proof
    cJ
    ctop
    wcel
    #
    cJ
    ccl
    cfv
    va
    cJ
    cuni
    #
    cpw
    va
    cv
    vb
    cv
    wss
    vb
    cJ
    ccld
    cfv
    #
    crab
    cint
    cmpt
    #
    cF
    va
    vb
    cJ
    @1
    @1
    eqid
    #
    clsfval
    @0
    @2
    @1
    cmre
    cfv
    wcel
    cF
    @3
    wceq
    cJ
    @1
    @4
    cldmre
    va
    @2
    cF
    @1
    vb
    mrccls.f
    mrcfval
    syl
    eqtr4d
end
