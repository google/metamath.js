include "cmnd.mm"
include "wcel.mm"
include "csubmnd.mm"
include "cfv.mm"
include "wss.mm"
include "c0g.mm"
include "cress.mm"
include "co.mm"
include "ssid.mm"
include "a1i.mm"
include "eqid.mm"
include "mndidcl.mm"
include "ressid.mm"
include "id.mm"
include "eqeltrd.mm"
include "issubm2.mm"
include "mpbir3and.mm"

theorem submid
  let cB: class B
  let cM: class M
  assume submss.b: |- B = ( Base ` M )


  assert |- ( M e. Mnd -> B e. ( SubMnd ` M ) )

  proof
    cM
    cmnd
    wcel
    #
    cB
    cM
    csubmnd
    cfv
    wcel
    cB
    cB
    wss
    #
    cM
    c0g
    cfv
    #
    cB
    wcel
    cM
    cB
    cress
    co
    #
    cmnd
    wcel
    @1
    @0
    cB
    ssid
    a1i
    cB
    cM
    @2
    submss.b
    @2
    eqid
    #
    mndidcl
    @0
    @3
    cM
    cmnd
    cB
    cM
    cmnd
    submss.b
    ressid
    @0
    id
    eqeltrd
    cB
    cB
    @3
    cM
    @2
    submss.b
    @4
    @3
    eqid
    issubm2
    mpbir3and
end
