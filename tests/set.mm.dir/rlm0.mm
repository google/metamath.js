include "c0g.mm"
include "cfv.mm"
include "crglmod.mm"
include "wceq.mm"
include "wtru.mm"
include "cbs.mm"
include "csra.mm"
include "rlmval.mm"
include "a1i.mm"
include "eqidd.mm"
include "wss.mm"
include "ssid.mm"
include "sralmod0.mm"
include "trud.mm"

theorem rlm0
  let cR: class R


  assert |- ( 0g ` R ) = ( 0g ` ( ringLMod ` R ) )

  proof
    cR
    c0g
    cfv
    #
    cR
    crglmod
    cfv
    #
    c0g
    cfv
    wceq
    wtru
    @1
    cR
    cbs
    cfv
    #
    cR
    @0
    @1
    @2
    cR
    csra
    cfv
    cfv
    wceq
    wtru
    cR
    rlmval
    a1i
    wtru
    @0
    eqidd
    @2
    @2
    wss
    wtru
    @2
    ssid
    a1i
    sralmod0
    trud
end
