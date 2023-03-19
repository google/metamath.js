include "cuni.mm"
include "eqid.mm"
include "toptopon.mm"

theorem toptopon2
  let cJ: class J


  assert |- ( J e. Top <-> J e. ( TopOn ` U. J ) )

  proof
    cJ
    cJ
    cuni
    #
    @0
    eqid
    toptopon
end
