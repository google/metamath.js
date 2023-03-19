include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "clgs.mm"
include "co.mm"
include "cv.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "eqid.mm"
include "lgscl2.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "elrab.mm"
include "simprbi.mm"
include "syl.mm"

theorem lgsle1
  let cA: class A
  let cN: class N
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cP: class P


  assert |- ( ( A e. ZZ /\ N e. ZZ ) -> ( abs ` ( A /L N ) ) <_ 1 )

  proof
    cA
    cz
    wcel
    cN
    cz
    wcel
    wa
    cA
    cN
    clgs
    co
    #
    vx
    cv
    #
    cabs
    cfv
    #
    c1
    cle
    wbr
    #
    vx
    cz
    crab
    #
    wcel
    #
    @0
    cabs
    cfv
    #
    c1
    cle
    wbr
    #
    vx
    cA
    cN
    @4
    @4
    eqid
    lgscl2
    @5
    @0
    cz
    wcel
    @7
    @3
    @7
    vx
    @0
    cz
    @1
    @0
    wceq
    @2
    @6
    c1
    cle
    @1
    @0
    cabs
    fveq2
    breq1d
    elrab
    simprbi
    syl
end
