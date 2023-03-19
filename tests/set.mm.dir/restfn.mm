include "cvv.mm"
include "cv.mm"
include "cin.mm"
include "cmpt.mm"
include "crn.mm"
include "crest.mm"
include "df-rest.mm"
include "vex.mm"
include "mptex.mm"
include "rnex.mm"
include "fnmpt2i.mm"

theorem restfn
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y


  assert |- |`t Fn ( _V X. _V )

  proof
    vj
    vx
    cvv
    cvv
    vy
    vj
    cv
    #
    vy
    cv
    vx
    cv
    cin
    #
    cmpt
    #
    crn
    crest
    vx
    vy
    vj
    df-rest
    @2
    vy
    @0
    @1
    vj
    vex
    mptex
    rnex
    fnmpt2i
end
