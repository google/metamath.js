include "wn.mm"
include "wa.mm"
include "wo.mm"
include "id.mm"
include "wi1.mm"
include "d4oa.mm"
include "oa4gto4u.mm"
include "oa4uto4.mm"
include "oa4to6.mm"

theorem d6oa
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  let wve: term e
  let wvf: term f
  assume d6oa.1: |- a =< b '
  assume d6oa.2: |- c =< d '
  assume d6oa.3: |- e =< f '


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
    d6oa.1
    d6oa.2
    d6oa.3
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
    @0
    @1
    @2
    @3
    @1
    @3
    wi1
    #
    @0
    @3
    wi1
    #
    @2
    @3
    wi1
    #
    @4
    @5
    @6
    @3
    @4
    @5
    wa
    @4
    @3
    wi1
    #
    @5
    @3
    wi1
    #
    wa
    wo
    #
    @4
    @6
    wa
    @7
    @6
    @3
    wi1
    #
    wa
    wo
    @5
    @6
    wa
    @8
    @10
    wa
    wo
    wa
    #
    @9
    id
    @11
    id
    d4oa
    @5
    id
    @4
    id
    @6
    id
    oa4gto4u
    oa4uto4
    oa4to6
end
