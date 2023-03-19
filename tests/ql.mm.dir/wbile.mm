include "wo.mm"
include "wr5-2v.mm"
include "oridm.mm"
include "bi1.mm"
include "wr2.mm"
include "wdf-le1.mm"

theorem wbile
  let wva: term a
  let wvb: term b
  assume wbile.1: |- ( a == b ) = 1


  assert |- ( a =<2 b ) = 1

  proof
    wva
    wvb
    wva
    wvb
    wo
    wvb
    wvb
    wo
    #
    wvb
    wva
    wvb
    wvb
    wbile.1
    wr5-2v
    @0
    wvb
    wvb
    oridm
    bi1
    wr2
    wdf-le1
end
