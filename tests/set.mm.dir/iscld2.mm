include "ctop.mm"
include "wcel.mm"
include "ccld.mm"
include "cfv.mm"
include "wss.mm"
include "cdif.mm"
include "iscld.mm"
include "baibd.mm"

theorem iscld2
  let cS: class S
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume iscld.1: |- X = U. J


  assert |- ( ( J e. Top /\ S C_ X ) -> ( S e. ( Clsd ` J ) <-> ( X \ S ) e. J ) )

  proof
    cJ
    ctop
    wcel
    cS
    cJ
    ccld
    cfv
    wcel
    cS
    cX
    wss
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
    baibd
end
