include "wi2.mm"
include "bile.mm"

theorem distoah1
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  let wve: term e
  let wvf: term f
  assume distoa.1: |- d = ( a ->2 b )
  assume distoa.2: |- e = ( ( b v c ) ->1 ( ( a ->2 b ) ^ ( a ->2 c ) ) )
  assume distoa.3: |- f = ( ( b v c ) ->2 ( ( a ->2 b ) ^ ( a ->2 c ) ) )


  assert |- d =< ( a ->2 b )

  proof
    wvd
    wva
    wvb
    wi2
    distoa.1
    bile
end
