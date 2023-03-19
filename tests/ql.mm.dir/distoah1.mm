include "wi2.mm"
include "bile.mm"

theorem distoah1
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  param wve: term e
  param wvf: term f
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
