include "wn.mm"
include "wi1.mm"
include "wa.mm"
include "wo.mm"
include "wt.mm"
include "oa3-u1lem.mm"
include "ax-r1.mm"
include "le1.mm"
include "u1lem9ab.mm"
include "ax-a2.mm"
include "lear.mm"
include "lel2or.mm"
include "df-le2.mm"
include "ax-r2.mm"
include "an1.mm"
include "ancom.mm"
include "u1lem8.mm"
include "2or.mm"
include "3tr.mm"
include "oa4to6dual.mm"
include "leid.mm"
include "letr.mm"
include "bltr.mm"

theorem oa3-u1
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume oa3-u1.1: |- ( ( c ->1 c ) ^ ( c v ( ( a ' ->1 c ) ^ ( ( ( c ^ ( a ' ->1 c ) ) v ( ( c ->1 c ) ^ ( ( a ' ->1 c ) ->1 c ) ) ) v ( ( ( c ^ ( b ' ->1 c ) ) v ( ( c ->1 c ) ^ ( ( b ' ->1 c ) ->1 c ) ) ) ^ ( ( ( a ' ->1 c ) ^ ( b ' ->1 c ) ) v ( ( ( a ' ->1 c ) ->1 c ) ^ ( ( b ' ->1 c ) ->1 c ) ) ) ) ) ) ) ) =< c


  assert |- ( c v ( ( a ' ->1 c ) ^ ( ( a ->1 c ) v ( ( b ->1 c ) ^ ( ( ( a ->1 c ) ^ ( b ->1 c ) ) v ( ( a ' ->1 c ) ^ ( b ' ->1 c ) ) ) ) ) ) ) =< c

  proof
    wvc
    wva
    wn
    #
    wvc
    wi1
    #
    wva
    wvc
    wi1
    #
    wvb
    wvc
    wi1
    #
    @2
    @3
    wa
    #
    @1
    wvb
    wn
    #
    wvc
    wi1
    #
    wa
    #
    wo
    wa
    wo
    wa
    wo
    #
    wt
    wvc
    @1
    wvc
    @1
    wa
    wt
    @2
    wa
    wo
    wvc
    @6
    wa
    wt
    @3
    wa
    wo
    @7
    @4
    wo
    wa
    wo
    wa
    wo
    wa
    #
    wvc
    @9
    @8
    wva
    wvb
    wvc
    oa3-u1lem
    ax-r1
    @9
    wvc
    wvc
    wvc
    wt
    @1
    @2
    @6
    @3
    wvc
    wvc
    wn
    le1
    wva
    wvc
    u1lem9ab
    wvb
    wvc
    u1lem9ab
    wvc
    wvc
    wvb
    wvc
    wa
    #
    @5
    wvc
    wa
    #
    wo
    #
    wo
    #
    wvc
    wt
    wa
    #
    @1
    @2
    wa
    #
    wo
    #
    @6
    @3
    wa
    #
    wo
    #
    @13
    wvc
    @13
    @12
    wvc
    wo
    wvc
    wvc
    @12
    ax-a2
    @12
    wvc
    @10
    wvc
    @11
    wvb
    wvc
    lear
    @5
    wvc
    lear
    lel2or
    df-le2
    ax-r2
    ax-r1
    @18
    @13
    @16
    wvc
    @17
    @12
    @16
    wvc
    wva
    wvc
    wa
    #
    @0
    wvc
    wa
    #
    wo
    #
    wo
    @21
    wvc
    wo
    wvc
    @14
    wvc
    @15
    @21
    wvc
    an1
    @15
    @2
    @1
    wa
    @21
    @1
    @2
    ancom
    wva
    wvc
    u1lem8
    ax-r2
    2or
    wvc
    @21
    ax-a2
    @21
    wvc
    @19
    wvc
    @20
    wva
    wvc
    lear
    @0
    wvc
    lear
    lel2or
    df-le2
    3tr
    @17
    @3
    @6
    wa
    @12
    @6
    @3
    ancom
    wvb
    wvc
    u1lem8
    ax-r2
    2or
    ax-r1
    ax-r2
    oa3-u1.1
    oa4to6dual
    wvc
    leid
    letr
    bltr
end
