include "con0.mm"
include "wcel.mm"
include "c0.mm"
include "coa.mm"
include "co.mm"
include "cvv.mm"
include "cv.mm"
include "csuc.mm"
include "cmpt.mm"
include "crdg.mm"
include "cfv.mm"
include "wceq.mm"
include "0elon.mm"
include "oav.mm"
include "mpan2.mm"
include "rdg0g.mm"
include "eqtrd.mm"

theorem oa0
  let cA: class A
  let vx: setvar x


  assert |- ( A e. On -> ( A +o (/) ) = A )

  proof
    cA
    con0
    wcel
    #
    cA
    c0
    coa
    co
    #
    c0
    vx
    cvv
    vx
    cv
    csuc
    cmpt
    #
    cA
    crdg
    cfv
    #
    cA
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
    oav
    mpan2
    cA
    con0
    @2
    rdg0g
    eqtrd
end
