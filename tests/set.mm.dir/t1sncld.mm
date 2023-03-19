include "ct1.mm"
include "wcel.mm"
include "csn.mm"
include "ccld.mm"
include "cfv.mm"
include "ctop.mm"
include "cv.mm"
include "wral.mm"
include "wi.mm"
include "ist1.mm"
include "wceq.mm"
include "sneq.mm"
include "eleq1d.mm"
include "rspccv.mm"
include "simplbiim.mm"
include "imp.mm"

theorem t1sncld
  let cA: class A
  let cJ: class J
  let cX: class X
  let vo: setvar o
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let va: setvar a
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let cP: class P
  let cQ: class Q
  assume ist0.1: |- X = U. J


  assert |- ( ( J e. Fre /\ A e. X ) -> { A } e. ( Clsd ` J ) )

  proof
    cJ
    ct1
    wcel
    #
    cA
    cX
    wcel
    #
    cA
    csn
    #
    cJ
    ccld
    cfv
    #
    wcel
    #
    @0
    cJ
    ctop
    wcel
    vx
    cv
    #
    csn
    #
    @3
    wcel
    #
    vx
    cX
    wral
    @1
    @4
    wi
    cJ
    cX
    vx
    ist0.1
    ist1
    @7
    @4
    vx
    cA
    cX
    @5
    cA
    wceq
    @6
    @2
    @3
    @5
    cA
    sneq
    eleq1d
    rspccv
    simplbiim
    imp
end
