include "ax-r5.mm"

theorem ror
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume lor.1: |- a = b


  assert |- ( a v c ) = ( b v c )

  proof
    wva
    wvb
    wvc
    lor.1
    ax-r5
end
