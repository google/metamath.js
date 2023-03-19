include "cds.mm"
include "cfv.mm"
include "crglmod.mm"
include "wceq.mm"
include "wtru.mm"
include "cbs.mm"
include "csra.mm"
include "rlmval.mm"
include "a1i.mm"
include "wss.mm"
include "ssid.mm"
include "srads.mm"
include "trud.mm"

theorem rlmds
  let cR: class R


  assert |- ( dist ` R ) = ( dist ` ( ringLMod ` R ) )

  proof
    cR
    cds
    cfv
    cR
    crglmod
    cfv
    #
    cds
    cfv
    wceq
    wtru
    @0
    cR
    cbs
    cfv
    #
    cR
    @0
    @1
    cR
    csra
    cfv
    cfv
    wceq
    wtru
    cR
    rlmval
    a1i
    @1
    @1
    wss
    wtru
    @1
    ssid
    a1i
    srads
    trud
end
