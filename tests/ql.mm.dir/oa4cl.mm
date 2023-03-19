include "wn.mm"
include "wa.mm"
include "wo.mm"
include "leor.mm"
include "oran2.mm"
include "lbtr.mm"
include "ax-oal4.mm"

theorem oa4cl
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d


  assert |- ( ( a v ( b ^ a ' ) ) ^ ( c v ( d ^ c ' ) ) ) =< ( ( b ^ a ' ) v ( a ^ ( c v ( ( a v c ) ^ ( ( b ^ a ' ) v ( d ^ c ' ) ) ) ) ) )

  proof
    wva
    wvb
    wva
    wn
    wa
    #
    wvc
    wvd
    wvc
    wn
    wa
    #
    wva
    wvb
    wn
    #
    wva
    wo
    @0
    wn
    wva
    @2
    leor
    wvb
    wva
    oran2
    lbtr
    wvc
    wvd
    wn
    #
    wvc
    wo
    @1
    wn
    wvc
    @3
    leor
    wvd
    wvc
    oran2
    lbtr
    ax-oal4
end
