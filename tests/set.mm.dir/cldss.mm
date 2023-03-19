include "ctop.mm"
include "wcel.mm"
include "ccld.mm"
include "cfv.mm"
include "wss.mm"
include "cldrcl.mm"
include "cdif.mm"
include "iscld.mm"
include "simprbda.mm"
include "mpancom.mm"

theorem cldss
  let cS: class S
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume iscld.1: |- X = U. J


  assert |- ( S e. ( Clsd ` J ) -> S C_ X )

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
    cS
    cX
    wss
    #
    cS
    cJ
    cldrcl
    @0
    @1
    @2
    cX
    cS
    cdif
    cJ
    wcel
    cS
    cJ
    cX
    iscld.1
    iscld
    simprbda
    mpancom
end
