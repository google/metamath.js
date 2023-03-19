include "ri3.mm"

theorem ud3lem0b
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume ud3lem0a.1: |- a = b


  assert |- ( a ->3 c ) = ( b ->3 c )

  proof
    wva
    wvb
    wvc
    ud3lem0a.1
    ri3
end
