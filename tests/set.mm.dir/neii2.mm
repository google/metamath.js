include "ctop.mm"
include "wcel.mm"
include "cnei.mm"
include "cfv.mm"
include "wa.mm"
include "cuni.mm"
include "wss.mm"
include "cv.mm"
include "wrex.mm"
include "eqid.mm"
include "neiss2.mm"
include "isnei.mm"
include "simpr.mm"
include "syl6bi.mm"
include "impancom.mm"
include "mpd.mm"

theorem neii2
  let cS: class S
  let vg: setvar g
  let cJ: class J
  let cN: class N
  let cR: class R

  disjoint J g
  disjoint N g
  disjoint S g
  disjoint R g
  assert |- ( ( J e. Top /\ N e. ( ( nei ` J ) ` S ) ) -> E. g e. J ( S C_ g /\ g C_ N ) )

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
    cJ
    cuni
    #
    wss
    #
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
    cS
    cJ
    cN
    @2
    @2
    eqid
    #
    neiss2
    @0
    @3
    @1
    @5
    @0
    @3
    wa
    @1
    cN
    @2
    wss
    #
    @5
    wa
    @5
    cS
    vg
    cJ
    cN
    @2
    @6
    isnei
    @7
    @5
    simpr
    syl6bi
    impancom
    mpd
end
