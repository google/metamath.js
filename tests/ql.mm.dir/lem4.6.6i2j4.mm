include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi2.mm"
include "wi4.mm"
include "wi0.mm"
include "ax-a2.mm"
include "ax-r5.mm"
include "ax-a3.mm"
include "ax-r1.mm"
include "lor.mm"
include "ancom.mm"
include "lan.mm"
include "oml.mm"
include "ax-r2.mm"
include "3tr.mm"
include "leao1.mm"
include "leao4.mm"
include "lel2or.mm"
include "leid.mm"
include "leor.mm"
include "lerr.mm"
include "lebi.mm"
include "df-i2.mm"
include "df-i4.mm"
include "2or.mm"
include "df-i0.mm"
include "3tr1.mm"

theorem lem4.6.6i2j4
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->2 b ) v ( a ->4 b ) ) = ( a ->0 b )

  proof
    wvb
    wva
    wn
    #
    wvb
    wn
    #
    wa
    #
    wo
    #
    wva
    wvb
    wa
    #
    @0
    wvb
    wa
    #
    wo
    #
    @0
    wvb
    wo
    #
    @1
    wa
    #
    wo
    #
    wo
    #
    @7
    wva
    wvb
    wi2
    #
    wva
    wvb
    wi4
    #
    wo
    wva
    wvb
    wi0
    @10
    @2
    wvb
    wo
    #
    @9
    wo
    @2
    wvb
    @9
    wo
    #
    wo
    #
    @7
    @3
    @13
    @9
    wvb
    @2
    ax-a2
    ax-r5
    @2
    wvb
    @9
    ax-a3
    @15
    @2
    wvb
    @6
    wo
    #
    @8
    wo
    #
    wo
    @2
    @6
    wvb
    wo
    #
    @8
    wo
    #
    wo
    #
    @7
    @14
    @17
    @2
    @17
    @14
    wvb
    @6
    @8
    ax-a3
    ax-r1
    lor
    @17
    @19
    @2
    @16
    @18
    @8
    wvb
    @6
    ax-a2
    ax-r5
    lor
    @20
    @2
    @6
    wvb
    @8
    wo
    #
    wo
    #
    wo
    @2
    @6
    @7
    wo
    #
    wo
    #
    @7
    @19
    @22
    @2
    @6
    wvb
    @8
    ax-a3
    lor
    @22
    @23
    @2
    @21
    @7
    @6
    @21
    wvb
    @1
    @7
    wa
    #
    wo
    wvb
    @1
    wvb
    @0
    wo
    #
    wa
    #
    wo
    #
    @7
    @8
    @25
    wvb
    @7
    @1
    ancom
    lor
    @25
    @27
    wvb
    @7
    @26
    @1
    @0
    wvb
    ax-a2
    lan
    lor
    @28
    @26
    @7
    wvb
    @0
    oml
    wvb
    @0
    ax-a2
    ax-r2
    3tr
    lor
    lor
    @24
    @7
    @2
    @7
    @23
    @0
    @1
    wvb
    leao1
    @6
    @7
    @7
    @4
    @7
    @5
    wvb
    wva
    @0
    leao4
    @0
    wvb
    wvb
    leao1
    lel2or
    @7
    leid
    lel2or
    lel2or
    @7
    @23
    @2
    @7
    @6
    leor
    lerr
    lebi
    3tr
    3tr
    3tr
    @11
    @3
    @12
    @9
    wva
    wvb
    df-i2
    wva
    wvb
    df-i4
    2or
    wva
    wvb
    df-i0
    3tr1
end
