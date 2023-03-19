include "wi1.mm"
include "wa.mm"
include "wo.mm"
include "wn.mm"
include "u1lem9a.mm"
include "lecon1.mm"
include "ax-a2.mm"
include "le2an.mm"
include "lelor.mm"
include "bltr.mm"
include "le2or.mm"
include "lelan.mm"
include "letr.mm"

theorem oa4uto4
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  assume oa4uto4.1: |- ( ( a ->1 d ) ^ ( ( a ' ->1 d ) v ( ( b ' ->1 d ) ^ ( ( ( ( a ->1 d ) ^ ( b ->1 d ) ) v ( ( a ' ->1 d ) ^ ( b ' ->1 d ) ) ) v ( ( ( ( a ->1 d ) ^ ( c ->1 d ) ) v ( ( a ' ->1 d ) ^ ( c ' ->1 d ) ) ) ^ ( ( ( b ->1 d ) ^ ( c ->1 d ) ) v ( ( b ' ->1 d ) ^ ( c ' ->1 d ) ) ) ) ) ) ) ) =< d


  assert |- ( ( a ->1 d ) ^ ( a v ( b ^ ( ( ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^ ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) ) ) ) ) =< d

  proof
    wva
    wvd
    wi1
    #
    wva
    wvb
    wva
    wvb
    wa
    #
    @0
    wvb
    wvd
    wi1
    #
    wa
    #
    wo
    #
    wva
    wvc
    wa
    #
    @0
    wvc
    wvd
    wi1
    #
    wa
    #
    wo
    #
    wvb
    wvc
    wa
    #
    @2
    @6
    wa
    #
    wo
    #
    wa
    #
    wo
    #
    wa
    #
    wo
    #
    wa
    @0
    wva
    wn
    wvd
    wi1
    #
    wvb
    wn
    wvd
    wi1
    #
    @3
    @16
    @17
    wa
    #
    wo
    #
    @7
    @16
    wvc
    wn
    wvd
    wi1
    #
    wa
    #
    wo
    #
    @10
    @17
    @20
    wa
    #
    wo
    #
    wa
    #
    wo
    #
    wa
    #
    wo
    #
    wa
    wvd
    @15
    @28
    @0
    wva
    @16
    @14
    @27
    @16
    wva
    wva
    wvd
    u1lem9a
    lecon1
    #
    wvb
    @17
    @13
    @26
    @17
    wvb
    wvb
    wvd
    u1lem9a
    lecon1
    #
    @4
    @19
    @12
    @25
    @4
    @3
    @1
    wo
    @19
    @1
    @3
    ax-a2
    @1
    @18
    @3
    wva
    @16
    wvb
    @17
    @29
    @30
    le2an
    lelor
    bltr
    @8
    @22
    @11
    @24
    @8
    @7
    @5
    wo
    @22
    @5
    @7
    ax-a2
    @5
    @21
    @7
    wva
    @16
    wvc
    @20
    @29
    @20
    wvc
    wvc
    wvd
    u1lem9a
    lecon1
    #
    le2an
    lelor
    bltr
    @11
    @10
    @9
    wo
    @24
    @9
    @10
    ax-a2
    @9
    @23
    @10
    wvb
    @17
    wvc
    @20
    @30
    @31
    le2an
    lelor
    bltr
    le2an
    le2or
    le2an
    le2or
    lelan
    oa4uto4.1
    letr
end
