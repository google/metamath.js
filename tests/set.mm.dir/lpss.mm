include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "clp.mm"
include "cfv.mm"
include "ccl.mm"
include "lpsscls.mm"
include "clsss3.mm"
include "sstrd.mm"

theorem lpss
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


  assert |- ( ( J e. Top /\ S C_ X ) -> ( ( limPt ` J ) ` S ) C_ X )

  proof
    cJ
    ctop
    wcel
    cS
    cX
    wss
    wa
    cS
    cJ
    clp
    cfv
    cfv
    cS
    cJ
    ccl
    cfv
    cfv
    cX
    cS
    cJ
    cX
    lpfval.1
    lpsscls
    cS
    cJ
    cX
    lpfval.1
    clsss3
    sstrd
end
