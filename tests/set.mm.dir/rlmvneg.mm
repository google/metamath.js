include "cminusg.mm"
include "cfv.mm"
include "crglmod.mm"
include "wceq.mm"
include "wtru.mm"
include "cbs.mm"
include "eqidd.mm"
include "rlmbas.mm"
include "a1i.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cplusg.mm"
include "rlmplusg.mm"
include "oveqd.mm"
include "grpinvpropd.mm"
include "trud.mm"

theorem rlmvneg
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( invg ` R ) = ( invg ` ( ringLMod ` R ) )

  proof
    cR
    cminusg
    cfv
    cR
    crglmod
    cfv
    #
    cminusg
    cfv
    wceq
    wtru
    vx
    vy
    cR
    cbs
    cfv
    #
    cR
    @0
    wtru
    @1
    eqidd
    @1
    @0
    cbs
    cfv
    wceq
    wtru
    cR
    rlmbas
    a1i
    wtru
    vx
    cv
    #
    @1
    wcel
    vy
    cv
    #
    @1
    wcel
    wa
    wa
    #
    cR
    cplusg
    cfv
    #
    @0
    cplusg
    cfv
    #
    @2
    @3
    @5
    @6
    wceq
    @4
    cR
    rlmplusg
    a1i
    oveqd
    grpinvpropd
    trud
end
