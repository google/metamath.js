include "cid.mm"
include "cvv.mm"
include "cv.mm"
include "cmpt.mm"
include "c1.mm"
include "crelexp.mm"
include "co.mm"
include "dfid4.mm"
include "relexp1g.mm"
include "mpteq2ia.mm"
include "eqtr4i.mm"

theorem dfid5
  let vx: setvar x


  assert |- _I = ( x e. _V |-> ( x ^r 1 ) )

  proof
    cid
    vx
    cvv
    vx
    cv
    #
    cmpt
    vx
    cvv
    @0
    c1
    crelexp
    co
    #
    cmpt
    vx
    dfid4
    vx
    cvv
    @1
    @0
    @0
    cvv
    relexp1g
    mpteq2ia
    eqtr4i
end
