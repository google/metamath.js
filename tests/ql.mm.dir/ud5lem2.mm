include "wn.mm"
include "wo.mm"
include "wi5.mm"
include "wa.mm"
include "df-i5.mm"
include "ax-a3.mm"
include "ancom.mm"
include "anabs.mm"
include "ax-r2.mm"
include "ax-a2.mm"
include "wf.mm"
include "anor2.mm"
include "ax-r1.mm"
include "ran.mm"
include "an32.mm"
include "anidm.mm"
include "dff.mm"
include "lan.mm"
include "an0.mm"
include "2or.mm"
include "or0.mm"

theorem ud5lem2
  param wva: term a
  param wvb: term b


  assert |- ( ( a v b ' ) ->5 a ) = ( a v ( a ' ^ b ) )

  proof
    wva
    wvb
    wn
    #
    wo
    #
    wva
    wi5
    @1
    wva
    wa
    #
    @1
    wn
    #
    wva
    wa
    #
    wo
    @3
    wva
    wn
    #
    wa
    #
    wo
    #
    wva
    @5
    wvb
    wa
    #
    wo
    #
    @1
    wva
    df-i5
    @7
    @2
    @4
    @6
    wo
    #
    wo
    @9
    @2
    @4
    @6
    ax-a3
    @2
    wva
    @10
    @8
    @2
    wva
    @1
    wa
    wva
    @1
    wva
    ancom
    wva
    @0
    anabs
    ax-r2
    @10
    @6
    @4
    wo
    #
    @8
    @4
    @6
    ax-a2
    @11
    @8
    wf
    wo
    @8
    @6
    @8
    @4
    wf
    @6
    @8
    @5
    wa
    #
    @8
    @3
    @8
    @5
    @8
    @3
    wva
    wvb
    anor2
    ax-r1
    #
    ran
    @12
    @5
    @5
    wa
    #
    wvb
    wa
    @8
    @5
    wvb
    @5
    an32
    @14
    @5
    wvb
    @5
    anidm
    ran
    ax-r2
    ax-r2
    @4
    @8
    wva
    wa
    #
    wf
    @3
    @8
    wva
    @13
    ran
    @15
    @5
    wva
    wa
    #
    wvb
    wa
    #
    wf
    @5
    wvb
    wva
    an32
    @17
    wvb
    @16
    wa
    #
    wf
    @16
    wvb
    ancom
    @18
    wvb
    wf
    wa
    wf
    @16
    wf
    wvb
    @16
    wva
    @5
    wa
    #
    wf
    @5
    wva
    ancom
    wf
    @19
    wva
    dff
    ax-r1
    ax-r2
    lan
    wvb
    an0
    ax-r2
    ax-r2
    ax-r2
    ax-r2
    2or
    @8
    or0
    ax-r2
    ax-r2
    2or
    ax-r2
    ax-r2
end
