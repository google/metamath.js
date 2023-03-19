include "ax-a2.mm"

theorem orcom
  param wva: term a
  param wvb: term b


  assert |- ( a v b ) = ( b v a )

  proof
    wva
    wvb
    ax-a2
end
