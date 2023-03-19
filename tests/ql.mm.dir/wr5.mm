include "wr5-2v.mm"

theorem wr5
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume wr5.1: |- ( a == b ) = 1


  assert |- ( ( a v c ) == ( b v c ) ) = 1

  proof
    wva
    wvb
    wvc
    wr5.1
    wr5-2v
end
