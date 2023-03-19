include "cr.mm"
include "cxp.mm"
include "ctx.mm"
include "co.mm"
include "cuni.mm"
include "tpr2tp.mm"
include "toponunii.mm"
include "eqcomi.mm"

theorem tpr2uni
  let cJ: class J
  assume tpr2tp.0: |- J = ( topGen ` ran (,) )


  assert |- U. ( J tX J ) = ( RR X. RR )

  proof
    cr
    cr
    cxp
    #
    cJ
    cJ
    ctx
    co
    #
    cuni
    @0
    @1
    cJ
    tpr2tp.0
    tpr2tp
    toponunii
    eqcomi
end
