include "wi5.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "df-i5.mm"
include "ran.mm"
include "comanr1.mm"
include "comcom3.mm"
include "com2or.mm"
include "fh1r.mm"
include "ax-a2.mm"
include "wf.mm"
include "an32.mm"
include "anidm.mm"
include "ax-r2.mm"
include "ancom.mm"
include "dff.mm"
include "lan.mm"
include "ax-r1.mm"
include "an0.mm"
include "2or.mm"
include "or0.mm"

theorem u5lemana
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->5 b ) ^ a ' ) = ( ( a ' ^ b ) v ( a ' ^ b ' ) )

  proof
    wva
    wvb
    wi5
    #
    wva
    wn
    #
    wa
    wva
    wvb
    wa
    #
    @1
    wvb
    wa
    #
    wo
    #
    @1
    wvb
    wn
    #
    wa
    #
    wo
    #
    @1
    wa
    #
    @3
    @6
    wo
    #
    @0
    @7
    @1
    wva
    wvb
    df-i5
    ran
    @8
    @4
    @1
    wa
    #
    @6
    @1
    wa
    #
    wo
    @9
    @1
    @4
    @6
    @1
    @2
    @3
    wva
    @2
    wva
    wvb
    comanr1
    comcom3
    #
    @1
    wvb
    comanr1
    #
    com2or
    @1
    @5
    comanr1
    fh1r
    @10
    @3
    @11
    @6
    @10
    @2
    @1
    wa
    #
    @3
    @1
    wa
    #
    wo
    #
    @3
    @1
    @2
    @3
    @12
    @13
    fh1r
    @16
    @15
    @14
    wo
    #
    @3
    @14
    @15
    ax-a2
    @17
    @3
    wf
    wo
    @3
    @15
    @3
    @14
    wf
    @15
    @1
    @1
    wa
    #
    wvb
    wa
    @3
    @1
    wvb
    @1
    an32
    @18
    @1
    wvb
    @1
    anidm
    #
    ran
    ax-r2
    @14
    wva
    @1
    wa
    #
    wvb
    wa
    #
    wf
    wva
    wvb
    @1
    an32
    @21
    wvb
    @20
    wa
    #
    wf
    @20
    wvb
    ancom
    @22
    wvb
    wf
    wa
    #
    wf
    @23
    @22
    wf
    @20
    wvb
    wva
    dff
    lan
    ax-r1
    wvb
    an0
    ax-r2
    ax-r2
    ax-r2
    2or
    @3
    or0
    ax-r2
    ax-r2
    ax-r2
    @11
    @18
    @5
    wa
    @6
    @1
    @5
    @1
    an32
    @18
    @1
    @5
    @19
    ran
    ax-r2
    2or
    ax-r2
    ax-r2
end
