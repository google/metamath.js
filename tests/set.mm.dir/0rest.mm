include "cvv.mm"
include "wcel.mm"
include "c0.mm"
include "crest.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cin.mm"
include "cmpt.mm"
include "crn.mm"
include "0ex.mm"
include "restval.mm"
include "mpan.mm"
include "mpt0.mm"
include "rneqi.mm"
include "rn0.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "cdm.mm"
include "wrel.mm"
include "cxp.mm"
include "relxp.mm"
include "wfn.mm"
include "restfn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "releqi.mm"
include "mpbir.mm"
include "ovprc2.mm"
include "pm2.61i.mm"

theorem 0rest
  let cA: class A
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cJ: class J
  let cS: class S


  assert |- ( (/) |`t A ) = (/)

  proof
    cA
    cvv
    wcel
    #
    c0
    cA
    crest
    co
    #
    c0
    wceq
    @0
    @1
    vx
    c0
    vx
    cv
    cA
    cin
    #
    cmpt
    #
    crn
    #
    c0
    c0
    cvv
    wcel
    @0
    @1
    @4
    wceq
    0ex
    vx
    cA
    c0
    cvv
    cvv
    restval
    mpan
    @4
    c0
    crn
    c0
    @3
    c0
    vx
    @2
    mpt0
    rneqi
    rn0
    eqtri
    syl6eq
    c0
    cA
    crest
    crest
    cdm
    #
    wrel
    cvv
    cvv
    cxp
    #
    wrel
    cvv
    cvv
    relxp
    @5
    @6
    crest
    @6
    wfn
    @5
    @6
    wceq
    restfn
    @6
    crest
    fndm
    ax-mp
    releqi
    mpbir
    ovprc2
    pm2.61i
end
