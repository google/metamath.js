include "cr.mm"
include "cxp.mm"
include "cvv.mm"
include "wcel.mm"
include "cc.mm"
include "cv.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cmpt2.mm"
include "wfo.mm"
include "reexALT.mm"
include "xpex.mm"
include "wf1o.mm"
include "eqid.mm"
include "cnref1o.mm"
include "f1ofo.mm"
include "ax-mp.mm"
include "fornex.mm"
include "mp2.mm"

theorem cnexALT
  let vx: setvar x
  let vy: setvar y


  assert |- CC e. _V

  proof
    cr
    cr
    cxp
    #
    cvv
    wcel
    @0
    cc
    vx
    vy
    cr
    cr
    vx
    cv
    ci
    vy
    cv
    cmul
    co
    caddc
    co
    cmpt2
    #
    wfo
    #
    cc
    cvv
    wcel
    cr
    cr
    reexALT
    reexALT
    xpex
    @0
    cc
    @1
    wf1o
    @2
    vx
    vy
    @1
    @1
    eqid
    cnref1o
    @0
    cc
    @1
    f1ofo
    ax-mp
    @0
    cc
    cvv
    @1
    fornex
    mp2
end
