include "cmgm.mm"
include "wcel.mm"
include "csubmgm.mm"
include "cfv.mm"
include "wss.mm"
include "cress.mm"
include "co.mm"
include "ssid.mm"
include "a1i.mm"
include "ressid.mm"
include "id.mm"
include "eqeltrd.mm"
include "eqid.mm"
include "issubmgm2.mm"
include "mpbir2and.mm"

theorem submgmid
  let cB: class B
  let cM: class M
  let vk: setvar k
  let vx: setvar x
  assume submgmss.b: |- B = ( Base ` M )


  assert |- ( M e. Mgm -> B e. ( SubMgm ` M ) )

  proof
    cM
    cmgm
    wcel
    #
    cB
    cM
    csubmgm
    cfv
    wcel
    cB
    cB
    wss
    #
    cM
    cB
    cress
    co
    #
    cmgm
    wcel
    @1
    @0
    cB
    ssid
    a1i
    @0
    @2
    cM
    cmgm
    cB
    cM
    cmgm
    submgmss.b
    ressid
    @0
    id
    eqeltrd
    cB
    cB
    @2
    cM
    submgmss.b
    @2
    eqid
    issubmgm2
    mpbir2and
end
