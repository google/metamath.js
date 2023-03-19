include "cpw.mm"
include "wss.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "co.mm"
include "topnval.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "restid2.mm"
include "mpan.mm"
include "syl5reqr.mm"

theorem topnid
  let cB: class B
  let cJ: class J
  let cW: class W
  let vw: setvar w
  assume topnval.1: |- B = ( Base ` W )
  assume topnval.2: |- J = ( TopSet ` W )


  assert |- ( J C_ ~P B -> J = ( TopOpen ` W ) )

  proof
    cJ
    cB
    cpw
    wss
    #
    cW
    ctopn
    cfv
    cJ
    cB
    crest
    co
    #
    cJ
    cB
    cJ
    cW
    topnval.1
    topnval.2
    topnval
    cB
    cvv
    wcel
    @0
    @1
    cJ
    wceq
    cB
    cW
    cbs
    cfv
    cvv
    topnval.1
    cW
    cbs
    fvex
    eqeltri
    cB
    cJ
    cvv
    restid2
    mpan
    syl5reqr
end
