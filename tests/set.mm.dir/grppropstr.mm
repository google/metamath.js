include "cbs.mm"
include "cfv.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "eqeltrri.mm"
include "grpbase.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "cplusg.mm"
include "grpplusg.mm"
include "grpprop.mm"

theorem grppropstr
  let cB: class B
  let c.pl: class .+
  let cK: class K
  let cL: class L
  assume grppropstr.b: |- ( Base ` K ) = B
  assume grppropstr.p: |- ( +g ` K ) = .+
  assume grppropstr.l: |- L = { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. }


  assert |- ( K e. Grp <-> L e. Grp )

  proof
    cK
    cL
    cK
    cbs
    cfv
    #
    cB
    cL
    cbs
    cfv
    #
    grppropstr.b
    cB
    cvv
    wcel
    cB
    @1
    wceq
    @0
    cB
    cvv
    grppropstr.b
    cK
    cbs
    fvex
    eqeltrri
    cB
    c.pl
    cL
    cvv
    grppropstr.l
    grpbase
    ax-mp
    eqtri
    cK
    cplusg
    cfv
    #
    c.pl
    cL
    cplusg
    cfv
    #
    grppropstr.p
    c.pl
    cvv
    wcel
    c.pl
    @3
    wceq
    @2
    c.pl
    cvv
    grppropstr.p
    cK
    cplusg
    fvex
    eqeltrri
    cB
    c.pl
    cL
    cvv
    grppropstr.l
    grpplusg
    ax-mp
    eqtri
    grpprop
end
