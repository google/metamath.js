include "wt.mm"
include "or1.mm"
include "df-le1.mm"

theorem le1
  param wva: term a


  assert |- a =< 1

  proof
    wva
    wt
    wva
    or1
    df-le1
end
