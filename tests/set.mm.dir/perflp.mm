include "cperf.mm"
include "wcel.mm"
include "ctop.mm"
include "clp.mm"
include "cfv.mm"
include "wceq.mm"
include "isperf.mm"
include "simprbi.mm"

theorem perflp
  let cJ: class J
  let cX: class X
  let vj: setvar j
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cS: class S
  let cT: class T
  assume lpfval.1: |- X = U. J


  assert |- ( J e. Perf -> ( ( limPt ` J ) ` X ) = X )

  proof
    cJ
    cperf
    wcel
    cJ
    ctop
    wcel
    cX
    cJ
    clp
    cfv
    cfv
    cX
    wceq
    cJ
    cX
    lpfval.1
    isperf
    simprbi
end
