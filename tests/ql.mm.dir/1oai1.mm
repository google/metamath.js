include "wn.mm"
include "wi2.mm"
include "wo.mm"
include "wa.mm"
include "wi1.mm"
include "1oa.mm"
include "i1i2.mm"
include "oran3.mm"
include "ax-r1.mm"
include "2an.mm"
include "ud1lem0ab.mm"
include "le3tr1.mm"

theorem 1oai1
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( ( a ->1 c ) ^ ( ( a ^ b ) ' ->1 ( ( a ->1 c ) ^ ( b ->1 c ) ) ) ) =< ( b ->1 c )

  proof
    wvc
    wn
    #
    wva
    wn
    #
    wi2
    #
    @1
    wvb
    wn
    #
    wo
    #
    @2
    @0
    @3
    wi2
    #
    wa
    #
    wi1
    #
    wa
    @5
    wva
    wvc
    wi1
    #
    wva
    wvb
    wa
    wn
    #
    @8
    wvb
    wvc
    wi1
    #
    wa
    #
    wi1
    #
    wa
    @10
    @0
    @1
    @3
    1oa
    @8
    @2
    @12
    @7
    wva
    wvc
    i1i2
    #
    @9
    @4
    @11
    @6
    @4
    @9
    wva
    wvb
    oran3
    ax-r1
    @8
    @2
    @10
    @5
    @13
    wvb
    wvc
    i1i2
    #
    2an
    ud1lem0ab
    2an
    @14
    le3tr1
end
