include "cr.mm"
include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ctx.mm"
include "co.mm"
include "cxp.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "retopon.mm"
include "eqeltri.mm"
include "txtopon.mm"
include "mp2an.mm"

theorem tpr2tp
  let cJ: class J
  assume tpr2tp.0: |- J = ( topGen ` ran (,) )


  assert |- ( J tX J ) e. ( TopOn ` ( RR X. RR ) )

  proof
    cJ
    cr
    ctopon
    cfv
    #
    wcel
    #
    @1
    cJ
    cJ
    ctx
    co
    cr
    cr
    cxp
    ctopon
    cfv
    wcel
    cJ
    cioo
    crn
    ctg
    cfv
    @0
    tpr2tp.0
    retopon
    eqeltri
    #
    @2
    cJ
    cJ
    cr
    cr
    txtopon
    mp2an
end
