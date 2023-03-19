include "ctps.mm"
include "wcel.mm"
include "ctop.mm"
include "cbs.mm"
include "cfv.mm"
include "cuni.mm"
include "wceq.mm"
include "eqid.mm"
include "istps2.mm"
include "simplbi.mm"

theorem tpstop
  let cJ: class J
  let cK: class K
  assume tpstop.j: |- J = ( TopOpen ` K )


  assert |- ( K e. TopSp -> J e. Top )

  proof
    cK
    ctps
    wcel
    cJ
    ctop
    wcel
    cK
    cbs
    cfv
    #
    cJ
    cuni
    wceq
    @0
    cJ
    cK
    @0
    eqid
    tpstop.j
    istps2
    simplbi
end
