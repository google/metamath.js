include "wi5.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "df-i5.mm"
include "ax-r5.mm"
include "ax-a3.mm"
include "lear.mm"
include "lel2or.mm"
include "leor.mm"
include "letr.mm"
include "df-le2.mm"
include "ax-r2.mm"

theorem u5lemob
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->5 b ) v b ) = ( ( a ' ^ b ' ) v b )

  proof
    wva
    wvb
    wi5
    #
    wvb
    wo
    wva
    wvb
    wa
    #
    wva
    wn
    #
    wvb
    wa
    #
    wo
    #
    @2
    wvb
    wn
    wa
    #
    wo
    #
    wvb
    wo
    #
    @5
    wvb
    wo
    #
    @0
    @6
    wvb
    wva
    wvb
    df-i5
    ax-r5
    @7
    @4
    @8
    wo
    @8
    @4
    @5
    wvb
    ax-a3
    @4
    @8
    @4
    wvb
    @8
    @1
    wvb
    @3
    wva
    wvb
    lear
    @2
    wvb
    lear
    lel2or
    wvb
    @5
    leor
    letr
    df-le2
    ax-r2
    ax-r2
end
