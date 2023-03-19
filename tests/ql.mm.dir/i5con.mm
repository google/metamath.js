include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wi5.mm"
include "ancom.mm"
include "ax-a2.mm"
include "ax-a1.mm"
include "ran.mm"
include "ax-r2.mm"
include "2an.mm"
include "2or.mm"
include "ax-a3.mm"
include "3tr1.mm"
include "df-i5.mm"

theorem i5con
  param wva: term a
  param wvb: term b


  assert |- ( a ->5 b ) = ( b ' ->5 a ' )

  proof
    wva
    wvb
    wa
    #
    wva
    wn
    #
    wvb
    wa
    #
    wo
    #
    @1
    wvb
    wn
    #
    wa
    #
    wo
    #
    @4
    @1
    wa
    #
    @4
    wn
    #
    @1
    wa
    #
    wo
    @8
    @1
    wn
    #
    wa
    #
    wo
    #
    wva
    wvb
    wi5
    @4
    @1
    wi5
    @5
    @3
    wo
    @7
    @9
    @11
    wo
    #
    wo
    @6
    @12
    @5
    @7
    @3
    @13
    @1
    @4
    ancom
    @3
    @2
    @0
    wo
    @13
    @0
    @2
    ax-a2
    @2
    @9
    @0
    @11
    @2
    wvb
    @1
    wa
    @9
    @1
    wvb
    ancom
    wvb
    @8
    @1
    wvb
    ax-a1
    #
    ran
    ax-r2
    @0
    wvb
    wva
    wa
    @11
    wva
    wvb
    ancom
    wvb
    @8
    wva
    @10
    @14
    wva
    ax-a1
    2an
    ax-r2
    2or
    ax-r2
    2or
    @3
    @5
    ax-a2
    @7
    @9
    @11
    ax-a3
    3tr1
    wva
    wvb
    df-i5
    @4
    @1
    df-i5
    3tr1
end
