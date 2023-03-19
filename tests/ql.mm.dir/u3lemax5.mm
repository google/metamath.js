include "wi3.mm"
include "wn.mm"
include "wo.mm"
include "wt.mm"
include "lem4.mm"
include "tb.mm"
include "lor.mm"
include "ax-a3.mm"
include "ax-r1.mm"
include "wa.mm"
include "oran3.mm"
include "u3lembi.mm"
include "ax-r4.mm"
include "ax-r2.mm"
include "ax-r5.mm"
include "le1.mm"
include "ska2.mm"
include "lea.mm"
include "bltr.mm"
include "lelor.mm"
include "lebi.mm"

theorem u3lemax5
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( ( a ->3 b ) ->3 ( ( a ->3 b ) ->3 ( ( b ->3 a ) ->3 ( ( b ->3 a ) ->3 ( ( b ->3 c ) ->3 ( ( b ->3 c ) ->3 ( ( c ->3 b ) ->3 ( ( c ->3 b ) ->3 ( a ->3 c ) ) ) ) ) ) ) ) ) = 1

  proof
    wva
    wvb
    wi3
    #
    @0
    wvb
    wva
    wi3
    #
    @1
    wvb
    wvc
    wi3
    #
    @2
    wvc
    wvb
    wi3
    #
    @3
    wva
    wvc
    wi3
    #
    wi3
    wi3
    #
    wi3
    wi3
    #
    wi3
    wi3
    #
    wi3
    wi3
    @0
    wn
    #
    @7
    wo
    #
    wt
    @0
    @7
    lem4
    @9
    @8
    @1
    wn
    #
    wvb
    wvc
    tb
    #
    wn
    #
    @4
    wo
    #
    wo
    #
    wo
    #
    wt
    @7
    @14
    @8
    @7
    @10
    @6
    wo
    @14
    @1
    @6
    lem4
    @6
    @13
    @10
    @6
    @2
    wn
    #
    @5
    wo
    #
    @13
    @2
    @5
    lem4
    @17
    @16
    @3
    wn
    #
    @4
    wo
    #
    wo
    #
    @13
    @5
    @19
    @16
    @3
    @4
    lem4
    lor
    @20
    @16
    @18
    wo
    #
    @4
    wo
    #
    @13
    @22
    @20
    @16
    @18
    @4
    ax-a3
    ax-r1
    @21
    @12
    @4
    @21
    @2
    @3
    wa
    #
    wn
    @12
    @2
    @3
    oran3
    @23
    @11
    wvb
    wvc
    u3lembi
    ax-r4
    ax-r2
    ax-r5
    ax-r2
    ax-r2
    ax-r2
    lor
    ax-r2
    lor
    @15
    @8
    @10
    wo
    #
    @13
    wo
    #
    wt
    @25
    @15
    @8
    @10
    @13
    ax-a3
    ax-r1
    @25
    wva
    wvb
    tb
    #
    wn
    #
    @13
    wo
    #
    wt
    @24
    @27
    @13
    @24
    @0
    @1
    wa
    #
    wn
    @27
    @0
    @1
    oran3
    @29
    @26
    wva
    wvb
    u3lembi
    ax-r4
    ax-r2
    ax-r5
    @28
    wt
    @28
    le1
    wt
    @27
    @12
    wva
    wvc
    tb
    #
    wo
    #
    wo
    #
    @28
    @32
    wt
    wva
    wvb
    wvc
    ska2
    ax-r1
    @31
    @13
    @27
    @30
    @4
    @12
    @30
    @4
    wvc
    wva
    wi3
    #
    wa
    #
    @4
    @34
    @30
    wva
    wvc
    u3lembi
    ax-r1
    @4
    @33
    lea
    bltr
    lelor
    lelor
    bltr
    lebi
    ax-r2
    ax-r2
    ax-r2
    ax-r2
end
