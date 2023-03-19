include "cv.mm"
include "cuni.mm"
include "clp.mm"
include "cfv.mm"
include "wceq.mm"
include "ctop.mm"
include "cperf.mm"
include "fveq2.mm"
include "unieq.mm"
include "syl6eqr.mm"
include "fveq12d.mm"
include "eqeq12d.mm"
include "df-perf.mm"
include "elrab2.mm"

theorem isperf
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


  assert |- ( J e. Perf <-> ( J e. Top /\ ( ( limPt ` J ) ` X ) = X ) )

  proof
    vj
    cv
    #
    cuni
    #
    @0
    clp
    cfv
    #
    cfv
    #
    @1
    wceq
    cX
    cJ
    clp
    cfv
    #
    cfv
    #
    cX
    wceq
    vj
    cJ
    ctop
    cperf
    @0
    cJ
    wceq
    #
    @3
    @5
    @1
    cX
    @6
    @1
    cX
    @2
    @4
    @0
    cJ
    clp
    fveq2
    @6
    @1
    cJ
    cuni
    cX
    @0
    cJ
    unieq
    lpfval.1
    syl6eqr
    #
    fveq12d
    @7
    eqeq12d
    vj
    df-perf
    elrab2
end
