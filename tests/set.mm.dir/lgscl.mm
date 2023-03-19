include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "clgs.mm"
include "co.mm"
include "ssrab2.mm"
include "eqid.mm"
include "lgscl2.mm"
include "sseldi.mm"

theorem lgscl
  let cA: class A
  let cN: class N
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cP: class P


  assert |- ( ( A e. ZZ /\ N e. ZZ ) -> ( A /L N ) e. ZZ )

  proof
    cA
    cz
    wcel
    cN
    cz
    wcel
    wa
    vx
    cv
    cabs
    cfv
    c1
    cle
    wbr
    #
    vx
    cz
    crab
    #
    cz
    cA
    cN
    clgs
    co
    @0
    vx
    cz
    ssrab2
    vx
    cA
    cN
    @1
    @1
    eqid
    lgscl2
    sseldi
end
