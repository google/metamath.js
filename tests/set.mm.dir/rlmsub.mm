include "csg.mm"
include "cfv.mm"
include "crglmod.mm"
include "wceq.mm"
include "wtru.mm"
include "cbs.mm"
include "rlmbas.mm"
include "a1i.mm"
include "cplusg.mm"
include "rlmplusg.mm"
include "grpsubpropd.mm"
include "trud.mm"

theorem rlmsub
  let cR: class R


  assert |- ( -g ` R ) = ( -g ` ( ringLMod ` R ) )

  proof
    cR
    csg
    cfv
    cR
    crglmod
    cfv
    #
    csg
    cfv
    wceq
    wtru
    cR
    @0
    cR
    cbs
    cfv
    @0
    cbs
    cfv
    wceq
    wtru
    cR
    rlmbas
    a1i
    cR
    cplusg
    cfv
    @0
    cplusg
    cfv
    wceq
    wtru
    cR
    rlmplusg
    a1i
    grpsubpropd
    trud
end
