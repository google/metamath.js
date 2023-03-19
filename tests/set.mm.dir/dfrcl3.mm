include "crcl.mm"
include "cvv.mm"
include "cid.mm"
include "cv.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "cmpt.mm"
include "cc0.mm"
include "crelexp.mm"
include "co.mm"
include "c1.mm"
include "dfrcl2.mm"
include "wcel.mm"
include "relexp0g.mm"
include "relexp1g.mm"
include "uneq12d.mm"
include "mpteq2ia.mm"
include "eqtr4i.mm"

theorem dfrcl3
  let vx: setvar x


  assert |- r* = ( x e. _V |-> ( ( x ^r 0 ) u. ( x ^r 1 ) ) )

  proof
    crcl
    vx
    cvv
    cid
    vx
    cv
    #
    cdm
    @0
    crn
    cun
    cres
    #
    @0
    cun
    #
    cmpt
    vx
    cvv
    @0
    cc0
    crelexp
    co
    #
    @0
    c1
    crelexp
    co
    #
    cun
    #
    cmpt
    vx
    dfrcl2
    vx
    cvv
    @5
    @2
    @0
    cvv
    wcel
    @3
    @1
    @4
    @0
    @0
    cvv
    relexp0g
    @0
    cvv
    relexp1g
    uneq12d
    mpteq2ia
    eqtr4i
end
