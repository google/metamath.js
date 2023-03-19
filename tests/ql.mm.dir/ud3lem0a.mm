include "li3.mm"

theorem ud3lem0a
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume ud3lem0a.1: |- a = b


  assert |- ( c ->3 a ) = ( c ->3 b )

  proof
    wva
    wvb
    wvc
    ud3lem0a.1
    li3
end
