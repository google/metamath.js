include "cbs.mm"
include "c1.mm"
include "df-base.mm"
include "slotfn.mm"

theorem basfn



  assert |- Base Fn _V

  proof
    cbs
    c1
    df-base
    slotfn
end
