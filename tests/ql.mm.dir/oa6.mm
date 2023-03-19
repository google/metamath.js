include "wn.mm"
include "wa.mm"
include "wo.mm"
include "id.mm"
include "axoa4b.mm"
include "oa4to6.mm"

theorem oa6
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  param wve: term e
  param wvf: term f
  assume oa6.1: |- a =< b '
  assume oa6.2: |- c =< d '
  assume oa6.3: |- e =< f '


  assert |- ( ( ( a v b ) ^ ( c v d ) ) ^ ( e v f ) ) =< ( b v ( a ^ ( c v ( ( ( a v c ) ^ ( b v d ) ) ^ ( ( ( a v e ) ^ ( b v f ) ) v ( ( c v e ) ^ ( d v f ) ) ) ) ) ) )

  proof
    wva
    wvb
    wvc
    wvd
    wve
    wvf
    wva
    wn
    #
    wvb
    wn
    wa
    wvc
    wn
    #
    wvd
    wn
    wa
    wo
    wve
    wn
    #
    wvf
    wn
    wa
    wo
    #
    @0
    @1
    @2
    oa6.1
    oa6.2
    oa6.3
    @3
    id
    @0
    id
    @1
    id
    @2
    id
    @0
    @1
    @2
    @3
    axoa4b
    oa4to6
end
