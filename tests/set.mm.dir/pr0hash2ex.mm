include "c0.mm"
include "csn.mm"
include "cpr.mm"
include "chash.mm"
include "cfv.mm"
include "c2o.mm"
include "c2.mm"
include "df2o2.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "hash2.mm"
include "eqtri.mm"

theorem pr0hash2ex



  assert |- ( # ` { (/) , { (/) } } ) = 2

  proof
    c0
    c0
    csn
    cpr
    #
    chash
    cfv
    c2o
    chash
    cfv
    c2
    @0
    c2o
    chash
    c2o
    @0
    df2o2
    eqcomi
    fveq2i
    hash2
    eqtri
end
