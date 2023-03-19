include "wi2.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "df-i2.mm"
include "ran.mm"
include "ax-a2.mm"
include "coman1.mm"
include "comcom7.mm"
include "coman2.mm"
include "fh2r.mm"
include "wf.mm"
include "ancom.mm"
include "anass.mm"
include "ax-r1.mm"
include "dff.mm"
include "lan.mm"
include "an0.mm"
include "ax-r2.mm"
include "2or.mm"
include "or0.mm"

theorem u2lemaa
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->2 b ) ^ a ) = ( a ^ b )

  proof
    wva
    wvb
    wi2
    #
    wva
    wa
    wvb
    wva
    wn
    #
    wvb
    wn
    #
    wa
    #
    wo
    #
    wva
    wa
    #
    wva
    wvb
    wa
    #
    @0
    @4
    wva
    wva
    wvb
    df-i2
    ran
    @5
    @3
    wvb
    wo
    #
    wva
    wa
    #
    @6
    @4
    @7
    wva
    wvb
    @3
    ax-a2
    ran
    @8
    @3
    wva
    wa
    #
    wvb
    wva
    wa
    #
    wo
    #
    @6
    @3
    wva
    wvb
    @3
    wva
    @1
    @2
    coman1
    comcom7
    @3
    wvb
    @1
    @2
    coman2
    comcom7
    fh2r
    @11
    @10
    @9
    wo
    #
    @6
    @9
    @10
    ax-a2
    @12
    @6
    wf
    wo
    @6
    @10
    @6
    @9
    wf
    wvb
    wva
    ancom
    @9
    wva
    @3
    wa
    #
    wf
    @3
    wva
    ancom
    @13
    wva
    @1
    wa
    #
    @2
    wa
    #
    wf
    @15
    @13
    wva
    @1
    @2
    anass
    ax-r1
    @15
    @2
    @14
    wa
    #
    wf
    @14
    @2
    ancom
    @16
    @2
    wf
    wa
    wf
    @14
    wf
    @2
    wf
    @14
    wva
    dff
    ax-r1
    lan
    @2
    an0
    ax-r2
    ax-r2
    ax-r2
    ax-r2
    2or
    @6
    or0
    ax-r2
    ax-r2
    ax-r2
    ax-r2
    ax-r2
end
