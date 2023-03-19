include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wi4.mm"
include "wi2.mm"
include "wi0.mm"
include "ax-a3.mm"
include "ax-r1.mm"
include "ax-a2.mm"
include "ancom.mm"
include "lor.mm"
include "leor.mm"
include "oml2.mm"
include "3tr.mm"
include "ax-r5.mm"
include "ax-r2.mm"
include "leao4.mm"
include "leao1.mm"
include "lel2or.mm"
include "leid.mm"
include "leo.mm"
include "lerr.mm"
include "lebi.mm"
include "df-i4.mm"
include "df-i2.mm"
include "2or.mm"
include "df-i0.mm"
include "3tr1.mm"

theorem lem4.6.6i4j2
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->4 b ) v ( a ->2 b ) ) = ( a ->0 b )

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
    wo
    #
    wvb
    wn
    #
    wa
    #
    wo
    #
    wvb
    @1
    @5
    wa
    #
    wo
    #
    wo
    #
    @4
    wva
    wvb
    wi4
    #
    wva
    wvb
    wi2
    #
    wo
    wva
    wvb
    wi0
    @10
    @3
    @6
    @9
    wo
    #
    wo
    @3
    @4
    @8
    wo
    #
    wo
    #
    @4
    @3
    @6
    @9
    ax-a3
    @13
    @14
    @3
    @13
    @6
    wvb
    wo
    #
    @8
    wo
    #
    @14
    @17
    @13
    @6
    wvb
    @8
    ax-a3
    ax-r1
    @16
    @4
    @8
    @16
    wvb
    @6
    wo
    wvb
    @5
    @4
    wa
    #
    wo
    @4
    @6
    wvb
    ax-a2
    @6
    @18
    wvb
    @4
    @5
    ancom
    lor
    wvb
    @4
    wvb
    @1
    leor
    oml2
    3tr
    ax-r5
    ax-r2
    lor
    @15
    @4
    @3
    @4
    @14
    @0
    @4
    @2
    wvb
    wva
    @1
    leao4
    @1
    wvb
    wvb
    leao1
    lel2or
    @4
    @4
    @8
    @4
    leid
    @1
    @5
    wvb
    leao1
    lel2or
    lel2or
    @4
    @14
    @3
    @4
    @8
    leo
    lerr
    lebi
    3tr
    @11
    @7
    @12
    @9
    wva
    wvb
    df-i4
    wva
    wvb
    df-i2
    2or
    wva
    wvb
    df-i0
    3tr1
end
