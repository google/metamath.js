include "wss.mm"
include "wcel.mm"
include "cvv.mm"
include "cress.mm"
include "co.mm"
include "wceq.mm"
include "ssid.mm"
include "cbs.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "eqid.mm"
include "ressid2.mm"
include "mp3an13.mm"

theorem ressid
  let cB: class B
  let cW: class W
  let cX: class X
  assume ressid.1: |- B = ( Base ` W )


  assert |- ( W e. X -> ( W |`s B ) = W )

  proof
    cB
    cB
    wss
    cW
    cX
    wcel
    cB
    cvv
    wcel
    cW
    cB
    cress
    co
    #
    cW
    wceq
    cB
    ssid
    cB
    cW
    cbs
    cfv
    cvv
    ressid.1
    cW
    cbs
    fvex
    eqeltri
    cB
    cB
    @0
    cW
    cX
    cvv
    @0
    eqid
    ressid.1
    ressid2
    mp3an13
end
