include "wa.mm"
include "wo.mm"
include "wi1.mm"
include "oa3to4lem3.mm"
include "lear.mm"
include "lel2or.mm"
include "letr.mm"

theorem oa3to4lem4
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  let wvg: term g
  assume oa3to4lem.1: |- a ' =< b
  assume oa3to4lem.2: |- c ' =< d
  assume oa3to4lem.3: |- g = ( ( a ^ b ) v ( c ^ d ) )
  assume oa3to4lem.oa3: |- ( a ^ ( ( a ->1 g ) v ( ( c ->1 g ) ^ ( ( a ^ c ) v ( ( a ->1 g ) ^ ( c ->1 g ) ) ) ) ) ) =< ( ( a ^ g ) v ( c ^ g ) )


  assert |- ( a ^ ( b v ( d ^ ( ( a ^ c ) v ( b ^ d ) ) ) ) ) =< g

  proof
    wva
    wvb
    wvd
    wva
    wvc
    wa
    #
    wvb
    wvd
    wa
    wo
    wa
    wo
    wa
    wva
    wva
    wvg
    wi1
    #
    wvc
    wvg
    wi1
    #
    @0
    @1
    @2
    wa
    wo
    wa
    wo
    wa
    #
    wvg
    wva
    wvb
    wvc
    wvd
    wvg
    oa3to4lem.1
    oa3to4lem.2
    oa3to4lem.3
    oa3to4lem3
    @3
    wva
    wvg
    wa
    #
    wvc
    wvg
    wa
    #
    wo
    wvg
    oa3to4lem.oa3
    @4
    wvg
    @5
    wva
    wvg
    lear
    wvc
    wvg
    lear
    lel2or
    letr
    letr
end
