include "ctop.mm"
include "wcel.mm"
include "ccld.mm"
include "cfv.mm"
include "cdif.mm"
include "cldrcl.mm"
include "wss.mm"
include "iscld.mm"
include "simplbda.mm"
include "mpancom.mm"

theorem cldopn
  let cS: class S
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume iscld.1: |- X = U. J


  assert |- ( S e. ( Clsd ` J ) -> ( X \ S ) e. J )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cJ
    ccld
    cfv
    wcel
    #
    cX
    cS
    cdif
    cJ
    wcel
    #
    cS
    cJ
    cldrcl
    @0
    @1
    cS
    cX
    wss
    @2
    cS
    cJ
    cX
    iscld.1
    iscld
    simplbda
    mpancom
end
