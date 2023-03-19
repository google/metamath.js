include "wo.mm"
include "anabs.mm"
include "df2le1.mm"

theorem leo
  let wva: term a
  let wvb: term b


  assert |- a =< ( a v b )

  proof
    wva
    wva
    wvb
    wo
    wva
    wvb
    anabs
    df2le1
end
