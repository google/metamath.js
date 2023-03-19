include "ax-a2.mm"

theorem orcom
  let wva: term a
  let wvb: term b


  assert |- ( a v b ) = ( b v a )

  proof
    wva
    wvb
    ax-a2
end
