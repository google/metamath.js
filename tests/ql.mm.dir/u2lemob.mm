include "wi2.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "df-i2.mm"
include "ax-r5.mm"
include "or32.mm"
include "ax-a2.mm"
include "oridm.mm"
include "lor.mm"
include "ax-r2.mm"

theorem u2lemob
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->2 b ) v b ) = ( ( a ' ^ b ' ) v b )

  proof
    wva
    wvb
    wi2
    #
    wvb
    wo
    wvb
    wva
    wn
    wvb
    wn
    wa
    #
    wo
    #
    wvb
    wo
    #
    @1
    wvb
    wo
    #
    @0
    @2
    wvb
    wva
    wvb
    df-i2
    ax-r5
    @3
    wvb
    wvb
    wo
    #
    @1
    wo
    #
    @4
    wvb
    @1
    wvb
    or32
    @6
    @1
    @5
    wo
    @4
    @5
    @1
    ax-a2
    @5
    wvb
    @1
    wvb
    oridm
    lor
    ax-r2
    ax-r2
    ax-r2
end
