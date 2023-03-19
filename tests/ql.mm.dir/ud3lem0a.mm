include "li3.mm"

theorem ud3lem0a
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume ud3lem0a.1: |- a = b


  assert |- ( c ->3 a ) = ( c ->3 b )

  proof
    wva
    wvb
    wvc
    ud3lem0a.1
    li3
end
