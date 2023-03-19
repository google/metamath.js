include "leao.mm"
include "df-le1.mm"

theorem df2le1
  let wva: term a
  let wvb: term b
  assume df2le1.1: |- ( a ^ b ) = a


  assert |- a =< b

  proof
    wva
    wvb
    wva
    wvb
    wva
    df2le1.1
    leao
    df-le1
end
