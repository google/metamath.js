include "cv.mm"
include "csn.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "sneq.mm"
include "breq1d.mm"
include "vex.mm"
include "ensn1.mm"
include "vtoclg.mm"

theorem ensn1g
  let cA: class A
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> { A } ~~ 1o )

  proof
    vx
    cv
    #
    csn
    #
    c1o
    cen
    wbr
    cA
    csn
    #
    c1o
    cen
    wbr
    vx
    cA
    cV
    @0
    cA
    wceq
    @1
    @2
    c1o
    cen
    @0
    cA
    sneq
    breq1d
    @0
    vx
    vex
    ensn1
    vtoclg
end
