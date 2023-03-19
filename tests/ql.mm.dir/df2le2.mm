include "df-le2.mm"
include "leoa.mm"

theorem df2le2
  param wva: term a
  param wvb: term b
  assume df2le2.1: |- a =< b


  assert |- ( a ^ b ) = a

  proof
    wva
    wvb
    wvb
    wva
    wvb
    df2le2.1
    df-le2
    leoa
end
