include "wo.mm"
include "wa.mm"
include "ancom.mm"
include "ml.mm"
include "cm.mm"
include "lor.mm"
include "3tr.mm"

theorem vneulem5
  param wvu: term u
  param wvw: term w
  param wvx: term x
  param wvy: term y


  assert |- ( ( ( x v y ) v u ) ^ ( ( x v y ) v w ) ) = ( ( x v y ) v ( ( ( x v y ) v u ) ^ w ) )

  proof
    wvx
    wvy
    wo
    #
    wvu
    wo
    #
    @0
    wvw
    wo
    #
    wa
    @2
    @1
    wa
    #
    @0
    wvw
    @1
    wa
    #
    wo
    #
    @0
    @1
    wvw
    wa
    #
    wo
    @1
    @2
    ancom
    @5
    @3
    @0
    wvw
    wvu
    ml
    cm
    @4
    @6
    @0
    wvw
    @1
    ancom
    lor
    3tr
end
