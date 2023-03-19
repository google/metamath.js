include "wi1.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wt.mm"
include "oa3-u2lem.mm"
include "ax-r1.mm"
include "u1lem9ab.mm"
include "le1.mm"
include "or32.mm"
include "ancom.mm"
include "u1lem8.mm"
include "ax-r2.mm"
include "2or.mm"
include "an1.mm"
include "lear.mm"
include "lel2or.mm"
include "df-le2.mm"
include "3tr.mm"
include "oa4to6dual.mm"
include "bltr.mm"

theorem oa3-u2
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume oa3-u2.1: |- ( ( ( a ' ->1 c ) ->1 c ) ^ ( ( a ' ->1 c ) v ( c ^ ( ( ( ( a ' ->1 c ) ^ c ) v ( ( ( a ' ->1 c ) ->1 c ) ^ ( c ->1 c ) ) ) v ( ( ( ( a ' ->1 c ) ^ ( b ' ->1 c ) ) v ( ( ( a ' ->1 c ) ->1 c ) ^ ( ( b ' ->1 c ) ->1 c ) ) ) ^ ( ( c ^ ( b ' ->1 c ) ) v ( ( c ->1 c ) ^ ( ( b ' ->1 c ) ->1 c ) ) ) ) ) ) ) ) =< c


  assert |- ( ( a ->1 c ) ^ ( ( a ' ->1 c ) v ( c ^ ( ( a ->1 c ) v ( ( b ->1 c ) ^ ( ( ( a ->1 c ) ^ ( b ->1 c ) ) v ( ( a ' ->1 c ) ^ ( b ' ->1 c ) ) ) ) ) ) ) ) =< c

  proof
    wva
    wvc
    wi1
    #
    wva
    wn
    #
    wvc
    wi1
    #
    wvc
    @0
    wvb
    wvc
    wi1
    #
    @0
    @3
    wa
    #
    @2
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
    wa
    #
    @0
    @2
    wvc
    @2
    wvc
    wa
    @0
    wt
    wa
    wo
    @7
    @4
    wo
    wvc
    @6
    wa
    wt
    @3
    wa
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
    oa3-u2lem
    ax-r1
    @2
    @0
    wvc
    wt
    @6
    @3
    wvc
    wva
    wvc
    u1lem9ab
    wvc
    wn
    le1
    wvb
    wvc
    u1lem9ab
    @2
    @0
    wa
    #
    wvc
    wt
    wa
    #
    wo
    @6
    @3
    wa
    #
    wo
    #
    wvc
    @13
    @10
    @12
    wo
    #
    @11
    wo
    wva
    wvc
    wa
    #
    @1
    wvc
    wa
    #
    wo
    #
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
    wo
    wvc
    @10
    @11
    @12
    or32
    @14
    @21
    @11
    wvc
    @10
    @17
    @12
    @20
    @10
    @0
    @2
    wa
    @17
    @2
    @0
    ancom
    wva
    wvc
    u1lem8
    ax-r2
    @12
    @3
    @6
    wa
    @20
    @6
    @3
    ancom
    wvb
    wvc
    u1lem8
    ax-r2
    2or
    wvc
    an1
    2or
    @21
    wvc
    @17
    wvc
    @20
    @15
    wvc
    @16
    wva
    wvc
    lear
    @1
    wvc
    lear
    lel2or
    @18
    wvc
    @19
    wvb
    wvc
    lear
    @5
    wvc
    lear
    lel2or
    lel2or
    df-le2
    3tr
    ax-r1
    oa3-u2.1
    oa4to6dual
    bltr
end
