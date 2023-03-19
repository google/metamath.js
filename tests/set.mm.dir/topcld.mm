include "ctop.mm"
include "wcel.mm"
include "ccld.mm"
include "cfv.mm"
include "wss.mm"
include "cdif.mm"
include "wa.mm"
include "c0.mm"
include "difid.mm"
include "0opn.mm"
include "syl5eqel.mm"
include "ssid.mm"
include "jctil.mm"
include "iscld.mm"
include "mpbird.mm"

theorem topcld
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  assume iscld.1: |- X = U. J


  assert |- ( J e. Top -> X e. ( Clsd ` J ) )

  proof
    cJ
    ctop
    wcel
    #
    cX
    cJ
    ccld
    cfv
    wcel
    cX
    cX
    wss
    #
    cX
    cX
    cdif
    #
    cJ
    wcel
    #
    wa
    @0
    @3
    @1
    @0
    @2
    c0
    cJ
    cX
    difid
    cJ
    0opn
    syl5eqel
    cX
    ssid
    jctil
    cX
    cJ
    cX
    iscld.1
    iscld
    mpbird
end
