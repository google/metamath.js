include "cbs.mm"
include "cfv.mm"
include "crglmod.mm"
include "wceq.mm"
include "wtru.mm"
include "csra.mm"
include "rlmval.mm"
include "a1i.mm"
include "wss.mm"
include "ssid.mm"
include "srabase.mm"
include "trud.mm"

theorem rlmbas
  let cR: class R


  assert |- ( Base ` R ) = ( Base ` ( ringLMod ` R ) )

  proof
    cR
    cbs
    cfv
    #
    cR
    crglmod
    cfv
    #
    cbs
    cfv
    wceq
    wtru
    @1
    @0
    cR
    @1
    @0
    cR
    csra
    cfv
    cfv
    wceq
    wtru
    cR
    rlmval
    a1i
    @0
    @0
    wss
    wtru
    @0
    ssid
    a1i
    srabase
    trud
end
