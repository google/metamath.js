include "wi2.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "tb.mm"
include "lea.mm"
include "ax-a3.mm"
include "or12.mm"
include "anor3.mm"
include "ax-r5.mm"
include "ax-r2.mm"
include "leo.mm"
include "df-i2.mm"
include "ax-r1.mm"
include "lbtr.mm"
include "le2an.mm"
include "id.mm"
include "bile.mm"
include "lel2or.mm"
include "lelor.mm"
include "bltr.mm"
include "oal2.mm"
include "letr.mm"
include "u2lembi.mm"
include "dfb.mm"
include "i2bi.mm"
include "2an.mm"
include "2or.mm"
include "le3tr2.mm"

theorem mloa
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( ( a == b ) ^ ( ( b == c ) v ( ( b v ( a == b ) ) ^ ( c v ( a == c ) ) ) ) ) =< ( c v ( a == c ) )

  proof
    wva
    wvb
    wi2
    #
    wvb
    wva
    wi2
    #
    wa
    #
    wvb
    wvc
    wa
    #
    wvb
    wn
    #
    wvc
    wn
    #
    wa
    #
    wo
    #
    @0
    wva
    wvc
    wi2
    #
    wa
    #
    wo
    #
    wa
    #
    @8
    wva
    wvb
    tb
    #
    wvb
    wvc
    tb
    #
    wvb
    @12
    wo
    #
    wvc
    wva
    wvc
    tb
    wo
    #
    wa
    #
    wo
    #
    wa
    @15
    @11
    @0
    wvb
    wvc
    wo
    wn
    #
    @9
    wo
    #
    wa
    @8
    @2
    @0
    @10
    @19
    @0
    @1
    lea
    @10
    @18
    @3
    @9
    wo
    #
    wo
    #
    @19
    @10
    @3
    @6
    @9
    wo
    wo
    #
    @21
    @3
    @6
    @9
    ax-a3
    @22
    @6
    @20
    wo
    @21
    @3
    @6
    @9
    or12
    @6
    @18
    @20
    wvb
    wvc
    anor3
    ax-r5
    ax-r2
    ax-r2
    @20
    @9
    @18
    @3
    @9
    @9
    wvb
    @0
    wvc
    @8
    wvb
    wvb
    wva
    wn
    #
    @4
    wa
    #
    wo
    #
    @0
    wvb
    @24
    leo
    @0
    @25
    wva
    wvb
    df-i2
    ax-r1
    lbtr
    wvc
    wvc
    @23
    @5
    wa
    #
    wo
    #
    @8
    wvc
    @26
    leo
    @8
    @27
    wva
    wvc
    df-i2
    ax-r1
    lbtr
    le2an
    @9
    @9
    @9
    id
    bile
    lel2or
    lelor
    bltr
    le2an
    wva
    wvb
    wvc
    oal2
    letr
    @2
    @12
    @10
    @17
    wva
    wvb
    u2lembi
    @7
    @13
    @9
    @16
    @13
    @7
    wvb
    wvc
    dfb
    ax-r1
    @0
    @14
    @8
    @15
    wva
    wvb
    i2bi
    wva
    wvc
    i2bi
    #
    2an
    2or
    2an
    @28
    le3tr2
end
