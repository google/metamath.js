include "cperf.mm"
include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "wn.mm"
include "wral.mm"
include "ctop.mm"
include "isperf3.mm"
include "simprbi.mm"
include "wceq.mm"
include "sneq.mm"
include "eleq1d.mm"
include "notbid.mm"
include "rspccva.mm"
include "sylan.mm"

theorem perfi
  let cP: class P
  let cJ: class J
  let cX: class X
  let vj: setvar j
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cT: class T
  assume lpfval.1: |- X = U. J


  assert |- ( ( J e. Perf /\ P e. X ) -> -. { P } e. J )

  proof
    cJ
    cperf
    wcel
    #
    vx
    cv
    #
    csn
    #
    cJ
    wcel
    #
    wn
    #
    vx
    cX
    wral
    #
    cP
    cX
    wcel
    cP
    csn
    #
    cJ
    wcel
    #
    wn
    #
    @0
    cJ
    ctop
    wcel
    @5
    vx
    cJ
    cX
    lpfval.1
    isperf3
    simprbi
    @4
    @8
    vx
    cP
    cX
    @1
    cP
    wceq
    #
    @3
    @7
    @9
    @2
    @6
    cJ
    @1
    cP
    sneq
    eleq1d
    notbid
    rspccva
    sylan
end
