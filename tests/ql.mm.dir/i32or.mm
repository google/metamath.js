include "wo.mm"
include "i3ror.mm"
include "i3lor.mm"
include "binr2.mm"

theorem i32or
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  assume i32or.1: |- ( a ->3 b ) = 1
  assume i32or.2: |- ( c ->3 d ) = 1


  assert |- ( ( a v c ) ->3 ( b v d ) ) = 1

  proof
    wva
    wvc
    wo
    wvb
    wvc
    wo
    wvb
    wvd
    wo
    wva
    wvb
    wvc
    i32or.1
    i3ror
    wvc
    wvd
    wvb
    i32or.2
    i3lor
    binr2
end
