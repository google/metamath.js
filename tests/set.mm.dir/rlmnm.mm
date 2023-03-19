include "cbs.mm"
include "cfv.mm"
include "crglmod.mm"
include "wceq.mm"
include "cnm.mm"
include "rlmbas.mm"
include "id.mm"
include "cplusg.mm"
include "rlmplusg.mm"
include "a1i.mm"
include "cds.mm"
include "rlmds.mm"
include "nmpropd.mm"
include "ax-mp.mm"

theorem rlmnm
  let cR: class R


  assert |- ( norm ` R ) = ( norm ` ( ringLMod ` R ) )

  proof
    cR
    cbs
    cfv
    cR
    crglmod
    cfv
    #
    cbs
    cfv
    wceq
    #
    cR
    cnm
    cfv
    @0
    cnm
    cfv
    wceq
    cR
    rlmbas
    @1
    cR
    @0
    @1
    id
    cR
    cplusg
    cfv
    @0
    cplusg
    cfv
    wceq
    @1
    cR
    rlmplusg
    a1i
    cR
    cds
    cfv
    @0
    cds
    cfv
    wceq
    @1
    cR
    rlmds
    a1i
    nmpropd
    ax-mp
end
