include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccld.mm"
include "cfv.mm"
include "ccl.mm"
include "wceq.mm"
include "clp.mm"
include "iscld3.mm"
include "cun.mm"
include "clslp.mm"
include "eqeq1d.mm"
include "ssequn2.mm"
include "syl6bbr.mm"
include "bitrd.mm"

theorem cldlp
  let cS: class S
  let cJ: class J
  let cX: class X
  let vj: setvar j
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cT: class T
  assume lpfval.1: |- X = U. J


  assert |- ( ( J e. Top /\ S C_ X ) -> ( S e. ( Clsd ` J ) <-> ( ( limPt ` J ) ` S ) C_ S ) )

  proof
    cJ
    ctop
    wcel
    cS
    cX
    wss
    wa
    #
    cS
    cJ
    ccld
    cfv
    wcel
    cS
    cJ
    ccl
    cfv
    cfv
    #
    cS
    wceq
    #
    cS
    cJ
    clp
    cfv
    cfv
    #
    cS
    wss
    #
    cS
    cJ
    cX
    lpfval.1
    iscld3
    @0
    @2
    cS
    @3
    cun
    #
    cS
    wceq
    @4
    @0
    @1
    @5
    cS
    cS
    cJ
    cX
    lpfval.1
    clslp
    eqeq1d
    @3
    cS
    ssequn2
    syl6bbr
    bitrd
end
