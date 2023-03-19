include "ax-r5.mm"

theorem ror
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume lor.1: |- a = b


  assert |- ( a v c ) = ( b v c )

  proof
    wva
    wvb
    wvc
    lor.1
    ax-r5
end
