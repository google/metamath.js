include "wi1.mm"
include "wid3oa.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "df-id3oa.mm"
include "lan.mm"
include "3oa2.mm"
include "bltr.mm"

theorem 3oa3
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( ( a ->1 c ) ^ ( a == c ==OA b ) ) =< ( b ->1 c )

  proof
    wva
    wvc
    wi1
    #
    wva
    wvb
    wvc
    wid3oa
    #
    wa
    @0
    @0
    wvb
    wvc
    wi1
    #
    wa
    wva
    wn
    wvc
    wi1
    wvb
    wn
    wvc
    wi1
    wa
    wo
    #
    wa
    @2
    @1
    @3
    @0
    wva
    wvb
    wvc
    df-id3oa
    lan
    wva
    wvb
    wvc
    3oa2
    bltr
end
