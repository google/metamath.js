include "con0.mm"
include "wcel.mm"
include "c0.mm"
include "comu.mm"
include "co.mm"
include "cvv.mm"
include "cv.mm"
include "coa.mm"
include "cmpt.mm"
include "crdg.mm"
include "cfv.mm"
include "wceq.mm"
include "0elon.mm"
include "omv.mm"
include "mpan2.mm"
include "0ex.mm"
include "rdg0.mm"
include "syl6eq.mm"

theorem om0
  let cA: class A
  let vx: setvar x


  assert |- ( A e. On -> ( A .o (/) ) = (/) )

  proof
    cA
    con0
    wcel
    #
    cA
    c0
    comu
    co
    #
    c0
    vx
    cvv
    vx
    cv
    cA
    coa
    co
    cmpt
    #
    c0
    crdg
    cfv
    #
    c0
    @0
    c0
    con0
    wcel
    @1
    @3
    wceq
    0elon
    vx
    cA
    c0
    omv
    mpan2
    c0
    @2
    0ex
    rdg0
    syl6eq
end
