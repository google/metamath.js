include "ctop.mm"
include "wcel.mm"
include "cnei.mm"
include "cfv.mm"
include "wa.mm"
include "wss.mm"
include "neiss2.mm"
include "cv.mm"
include "wrex.mm"
include "isnei.mm"
include "simpl.mm"
include "syl6bi.mm"
include "impancom.mm"
include "mpd.mm"

theorem neii1
  let cS: class S
  let cJ: class J
  let cN: class N
  let cX: class X
  let vg: setvar g
  let vj: setvar j
  let vv: setvar v
  let vx: setvar x
  let cP: class P
  assume neifval.1: |- X = U. J


  assert |- ( ( J e. Top /\ N e. ( ( nei ` J ) ` S ) ) -> N C_ X )

  proof
    cJ
    ctop
    wcel
    #
    cN
    cS
    cJ
    cnei
    cfv
    cfv
    wcel
    #
    wa
    cS
    cX
    wss
    #
    cN
    cX
    wss
    #
    cS
    cJ
    cN
    cX
    neifval.1
    neiss2
    @0
    @2
    @1
    @3
    @0
    @2
    wa
    @1
    @3
    cS
    vg
    cv
    #
    wss
    @4
    cN
    wss
    wa
    vg
    cJ
    wrex
    #
    wa
    @3
    cS
    vg
    cJ
    cN
    cX
    neifval.1
    isnei
    @3
    @5
    simpl
    syl6bi
    impancom
    mpd
end
