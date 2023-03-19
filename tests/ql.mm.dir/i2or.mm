include "wi2.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "df-i2.mm"
include "lea.mm"
include "lecon.mm"
include "leran.mm"
include "lelor.mm"
include "bltr.mm"
include "lear.mm"
include "lel2or.mm"
include "ax-r1.mm"
include "lbtr.mm"

theorem i2or
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( ( a ->2 c ) v ( b ->2 c ) ) =< ( ( a ^ b ) ->2 c )

  proof
    wva
    wvc
    wi2
    #
    wvb
    wvc
    wi2
    #
    wo
    wvc
    wva
    wvb
    wa
    #
    wn
    #
    wvc
    wn
    #
    wa
    #
    wo
    #
    @2
    wvc
    wi2
    #
    @0
    @6
    @1
    @0
    wvc
    wva
    wn
    #
    @4
    wa
    #
    wo
    @6
    wva
    wvc
    df-i2
    @9
    @5
    wvc
    @8
    @3
    @4
    @2
    wva
    wva
    wvb
    lea
    lecon
    leran
    lelor
    bltr
    @1
    wvc
    wvb
    wn
    #
    @4
    wa
    #
    wo
    @6
    wvb
    wvc
    df-i2
    @11
    @5
    wvc
    @10
    @3
    @4
    @2
    wvb
    wva
    wvb
    lear
    lecon
    leran
    lelor
    bltr
    lel2or
    @7
    @6
    @2
    wvc
    df-i2
    ax-r1
    lbtr
end
