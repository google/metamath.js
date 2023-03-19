include "c0.mm"
include "csuc.mm"
include "csn.mm"
include "cun.mm"
include "df-suc.mm"
include "uncom.mm"
include "un0.mm"
include "3eqtri.mm"

theorem suc0



  assert |- suc (/) = { (/) }

  proof
    c0
    csuc
    c0
    c0
    csn
    #
    cun
    @0
    c0
    cun
    @0
    c0
    df-suc
    c0
    @0
    uncom
    @0
    un0
    3eqtri
end
