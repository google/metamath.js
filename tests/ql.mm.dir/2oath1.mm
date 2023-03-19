include "wi2.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "df-i2.mm"
include "lan.mm"
include "coman1.mm"
include "comorr2.mm"
include "comcom2.mm"
include "anor3.mm"
include "ax-r1.mm"
include "cbtr.mm"
include "fh2.mm"
include "wf.mm"
include "anass.mm"
include "anidm.mm"
include "ran.mm"
include "ax-r2.mm"
include "wt.mm"
include "oran.mm"
include "lor.mm"
include "2oalem1.mm"
include "ax-r4.mm"
include "df-a.mm"
include "df-f.mm"
include "3tr1.mm"
include "2or.mm"
include "or0.mm"
include "3tr.mm"

theorem 2oath1
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( ( a ->2 b ) ^ ( ( b v c ) ->2 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) = ( ( a ->2 b ) ^ ( a ->2 c ) )

  proof
    wva
    wvb
    wi2
    #
    wvb
    wvc
    wo
    #
    @0
    wva
    wvc
    wi2
    #
    wa
    #
    wi2
    #
    wa
    @0
    @3
    @1
    wn
    @3
    wn
    wa
    #
    wo
    #
    wa
    @0
    @3
    wa
    #
    @0
    @5
    wa
    #
    wo
    #
    @3
    @4
    @6
    @0
    @1
    @3
    df-i2
    lan
    @3
    @0
    @5
    @0
    @2
    coman1
    @3
    @1
    @3
    wo
    #
    wn
    #
    @5
    @3
    @10
    @1
    @3
    comorr2
    comcom2
    @5
    @11
    @1
    @3
    anor3
    ax-r1
    cbtr
    fh2
    @9
    @3
    wf
    wo
    @3
    @7
    @3
    @8
    wf
    @7
    @0
    @0
    wa
    #
    @2
    wa
    #
    @3
    @13
    @7
    @0
    @0
    @2
    anass
    ax-r1
    @12
    @0
    @2
    @0
    anidm
    ran
    ax-r2
    @0
    wn
    #
    @5
    wn
    #
    wo
    #
    wn
    wt
    wn
    @8
    wf
    @16
    wt
    @16
    @14
    @10
    wo
    #
    wt
    @17
    @16
    @10
    @15
    @14
    @1
    @3
    oran
    lor
    ax-r1
    wva
    wvb
    wvc
    2oalem1
    ax-r2
    ax-r4
    @0
    @5
    df-a
    df-f
    3tr1
    2or
    @3
    or0
    ax-r2
    3tr
end
