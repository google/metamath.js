include "wn.mm"
include "wi1.mm"
include "wa.mm"
include "wo.mm"
include "oran3.mm"
include "ax-r1.mm"
include "u1lem9a.mm"
include "le2or.mm"
include "bltr.mm"
include "an32.mm"
include "lea.mm"
include "leo.mm"
include "or32.mm"
include "lbtr.mm"
include "u1lemab.mm"
include "ax-a1.mm"
include "bile.mm"
include "leran.mm"
include "letr.mm"
include "lel2or.mm"
include "lelor.mm"
include "df-i1.mm"
include "2or.mm"
include "le3tr1.mm"

theorem sadm3
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( ( ( a ' ->1 c ) ^ ( b ' ->1 c ) ) ->1 c ) =< ( ( a ->1 c ) v ( b ->1 c ) )

  proof
    wva
    wn
    #
    wvc
    wi1
    #
    wvb
    wn
    #
    wvc
    wi1
    #
    wa
    #
    wn
    #
    @4
    wvc
    wa
    #
    wo
    #
    @0
    wva
    wvc
    wa
    #
    wo
    #
    @2
    wvb
    wvc
    wa
    #
    wo
    #
    wo
    #
    @4
    wvc
    wi1
    wva
    wvc
    wi1
    #
    wvb
    wvc
    wi1
    #
    wo
    @7
    @9
    @2
    wo
    #
    @12
    @7
    @0
    @2
    wo
    #
    @1
    wvc
    wa
    #
    wo
    @15
    @5
    @16
    @6
    @17
    @5
    @1
    wn
    #
    @3
    wn
    #
    wo
    #
    @16
    @20
    @5
    @1
    @3
    oran3
    ax-r1
    @18
    @0
    @19
    @2
    wva
    wvc
    u1lem9a
    wvb
    wvc
    u1lem9a
    le2or
    bltr
    @6
    @17
    @3
    wa
    @17
    @1
    @3
    wvc
    an32
    @17
    @3
    lea
    bltr
    le2or
    @16
    @15
    @17
    @16
    @16
    @8
    wo
    @15
    @16
    @8
    leo
    @0
    @2
    @8
    or32
    lbtr
    @17
    @9
    @15
    @17
    @0
    wvc
    wa
    #
    @0
    wn
    #
    wvc
    wa
    #
    wo
    @9
    @0
    wvc
    u1lemab
    @21
    @0
    @23
    @8
    @0
    wvc
    lea
    @22
    wva
    wvc
    @22
    wva
    wva
    @22
    wva
    ax-a1
    ax-r1
    bile
    leran
    le2or
    bltr
    @9
    @2
    leo
    letr
    lel2or
    letr
    @2
    @11
    @9
    @2
    @10
    leo
    lelor
    letr
    @4
    wvc
    df-i1
    @13
    @9
    @14
    @11
    wva
    wvc
    df-i1
    wvb
    wvc
    df-i1
    2or
    le3tr1
end
