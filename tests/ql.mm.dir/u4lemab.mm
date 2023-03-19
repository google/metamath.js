include "wi4.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "df-i4.mm"
include "ran.mm"
include "comanr2.mm"
include "com2or.mm"
include "comcom6.mm"
include "fh1r.mm"
include "wf.mm"
include "lear.mm"
include "lel2or.mm"
include "df2le2.mm"
include "an32.mm"
include "anass.mm"
include "dff.mm"
include "lan.mm"
include "ax-r1.mm"
include "an0.mm"
include "ax-r2.mm"
include "2or.mm"
include "or0.mm"

theorem u4lemab
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->4 b ) ^ b ) = ( ( a ^ b ) v ( a ' ^ b ) )

  proof
    wva
    wvb
    wi4
    #
    wvb
    wa
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
    wo
    #
    wvb
    wn
    #
    wa
    #
    wo
    #
    wvb
    wa
    #
    @4
    @0
    @8
    wvb
    wva
    wvb
    df-i4
    ran
    @9
    @4
    wvb
    wa
    #
    @7
    wvb
    wa
    #
    wo
    #
    @4
    wvb
    @4
    @7
    wvb
    @1
    @3
    wva
    wvb
    comanr2
    @2
    wvb
    comanr2
    com2or
    wvb
    @7
    @5
    @6
    comanr2
    comcom6
    fh1r
    @12
    @4
    wf
    wo
    @4
    @10
    @4
    @11
    wf
    @4
    wvb
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
    df2le2
    @11
    @5
    wvb
    wa
    @6
    wa
    #
    wf
    @5
    @6
    wvb
    an32
    @13
    @5
    wvb
    @6
    wa
    #
    wa
    #
    wf
    @5
    wvb
    @6
    anass
    @15
    @5
    wf
    wa
    #
    wf
    @16
    @15
    wf
    @14
    @5
    wvb
    dff
    lan
    ax-r1
    @5
    an0
    ax-r2
    ax-r2
    ax-r2
    2or
    @4
    or0
    ax-r2
    ax-r2
    ax-r2
end
