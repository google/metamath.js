include "wi2.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "df-i2.mm"
include "wf.mm"
include "ancom.mm"
include "u2lemnana.mm"
include "ax-r2.mm"
include "lor.mm"
include "or0.mm"

theorem u2lem5
  param wva: term a
  param wvb: term b


  assert |- ( a ->2 ( a ->2 b ) ) = ( a ->2 b )

  proof
    wva
    wva
    wvb
    wi2
    #
    wi2
    @0
    wva
    wn
    #
    @0
    wn
    #
    wa
    #
    wo
    #
    @0
    wva
    @0
    df-i2
    @4
    @0
    wf
    wo
    @0
    @3
    wf
    @0
    @3
    @2
    @1
    wa
    wf
    @1
    @2
    ancom
    wva
    wvb
    u2lemnana
    ax-r2
    lor
    @0
    or0
    ax-r2
    ax-r2
end
