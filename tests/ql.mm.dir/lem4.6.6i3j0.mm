include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi3.mm"
include "wi0.mm"
include "ax-a3.mm"
include "ax-r1.mm"
include "lor.mm"
include "ax-a2.mm"
include "omln.mm"
include "ax-r2.mm"
include "ax-r5.mm"
include "leid.mm"
include "leor.mm"
include "lel2or.mm"
include "leo.mm"
include "lebi.mm"
include "leao1.mm"
include "df-le2.mm"
include "3tr.mm"
include "df-i3.mm"
include "df-i0.mm"
include "2or.mm"
include "3tr1.mm"

theorem lem4.6.6i3j0
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->3 b ) v ( a ->0 b ) ) = ( a ->0 b )

  proof
    wva
    wn
    #
    wvb
    wa
    #
    @0
    wvb
    wn
    #
    wa
    #
    wo
    #
    wva
    @0
    wvb
    wo
    #
    wa
    #
    wo
    #
    @5
    wo
    #
    @5
    wva
    wvb
    wi3
    #
    wva
    wvb
    wi0
    #
    wo
    @10
    @8
    @4
    @6
    @5
    wo
    #
    wo
    @4
    @6
    @0
    wo
    #
    wvb
    wo
    #
    wo
    #
    @5
    @4
    @6
    @5
    ax-a3
    @11
    @13
    @4
    @13
    @11
    @6
    @0
    wvb
    ax-a3
    ax-r1
    lor
    @14
    @4
    @5
    wvb
    wo
    #
    wo
    @4
    @5
    wo
    @5
    @13
    @15
    @4
    @12
    @5
    wvb
    @12
    @0
    @6
    wo
    @5
    @6
    @0
    ax-a2
    wva
    wvb
    omln
    ax-r2
    ax-r5
    lor
    @15
    @5
    @4
    @15
    @5
    @5
    @5
    wvb
    @5
    leid
    wvb
    @0
    leor
    lel2or
    @5
    wvb
    leo
    lebi
    lor
    @4
    @5
    @1
    @5
    @3
    @0
    wvb
    wvb
    leao1
    @0
    @2
    wvb
    leao1
    lel2or
    df-le2
    3tr
    3tr
    @9
    @7
    @10
    @5
    wva
    wvb
    df-i3
    wva
    wvb
    df-i0
    #
    2or
    @16
    3tr1
end
