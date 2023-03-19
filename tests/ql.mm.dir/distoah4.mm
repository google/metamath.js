include "wi2.mm"
include "wa.mm"
include "wo.mm"
include "wn.mm"
include "leo.mm"
include "ran.mm"
include "df-i2.mm"
include "ax-r2.mm"
include "le3tr1.mm"

theorem distoah4
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  let wve: term e
  let wvf: term f
  assume distoa.1: |- d = ( a ->2 b )
  assume distoa.2: |- e = ( ( b v c ) ->1 ( ( a ->2 b ) ^ ( a ->2 c ) ) )
  assume distoa.3: |- f = ( ( b v c ) ->2 ( ( a ->2 b ) ^ ( a ->2 c ) ) )


  assert |- ( d ^ ( a ->2 c ) ) =< f

  proof
    wva
    wvb
    wi2
    #
    wva
    wvc
    wi2
    #
    wa
    #
    @2
    wvb
    wvc
    wo
    #
    wn
    @2
    wn
    wa
    #
    wo
    #
    wvd
    @1
    wa
    wvf
    @2
    @4
    leo
    wvd
    @0
    @1
    distoa.1
    ran
    wvf
    @3
    @2
    wi2
    @5
    distoa.3
    @3
    @2
    df-i2
    ax-r2
    le3tr1
end
