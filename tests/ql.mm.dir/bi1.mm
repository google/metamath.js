include "tb.mm"
include "wt.mm"
include "rbi.mm"
include "biid.mm"
include "ax-r2.mm"

theorem bi1
  let wva: term a
  let wvb: term b
  assume bi1.1: |- a = b


  assert |- ( a == b ) = 1

  proof
    wva
    wvb
    tb
    wvb
    wvb
    tb
    wt
    wva
    wvb
    wvb
    bi1.1
    rbi
    wvb
    biid
    ax-r2
end
