include "wa.mm"
include "wo.mm"
include "ancom.mm"
include "ror.mm"
include "orcom.mm"
include "ml2i.mm"
include "3tr.mm"
include "ran.mm"

theorem mli
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume mli.1: |- c =< a


  assert |- ( ( a ^ b ) v c ) = ( a ^ ( b v c ) )

  proof
    wva
    wvb
    wa
    #
    wvc
    wo
    #
    wvc
    wvb
    wo
    #
    wva
    wa
    #
    wvb
    wvc
    wo
    #
    wva
    wa
    wva
    @4
    wa
    @1
    wvb
    wva
    wa
    #
    wvc
    wo
    wvc
    @5
    wo
    @3
    @0
    @5
    wvc
    wva
    wvb
    ancom
    ror
    @5
    wvc
    orcom
    wva
    wvb
    wvc
    mli.1
    ml2i
    3tr
    @2
    @4
    wva
    wvc
    wvb
    orcom
    ran
    @4
    wva
    ancom
    3tr
end
