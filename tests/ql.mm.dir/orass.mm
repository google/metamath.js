include "ax-a3.mm"

theorem orass
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( ( a v b ) v c ) = ( a v ( b v c ) )

  proof
    wva
    wvb
    wvc
    ax-a3
end
