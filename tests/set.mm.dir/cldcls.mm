include "ccld.mm"
include "cfv.mm"
include "wcel.mm"
include "ccl.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "cint.mm"
include "ctop.mm"
include "cuni.mm"
include "wceq.mm"
include "cldrcl.mm"
include "eqid.mm"
include "cldss.mm"
include "clsval.mm"
include "syl2anc.mm"
include "intmin.mm"
include "eqtrd.mm"

theorem cldcls
  let cS: class S
  let cJ: class J
  let cA: class A
  let vx: setvar x


  assert |- ( S e. ( Clsd ` J ) -> ( ( cls ` J ) ` S ) = S )

  proof
    cS
    cJ
    ccld
    cfv
    #
    wcel
    #
    cS
    cJ
    ccl
    cfv
    cfv
    #
    cS
    vx
    cv
    wss
    vx
    @0
    crab
    cint
    #
    cS
    @1
    cJ
    ctop
    wcel
    cS
    cJ
    cuni
    #
    wss
    @2
    @3
    wceq
    cS
    cJ
    cldrcl
    cS
    cJ
    @4
    @4
    eqid
    #
    cldss
    vx
    cS
    cJ
    @4
    @5
    clsval
    syl2anc
    vx
    cS
    @0
    intmin
    eqtrd
end
