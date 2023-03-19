include "wi3.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "df-i3.mm"
include "ran.mm"
include "comanr2.mm"
include "comcom3.mm"
include "com2or.mm"
include "comcom.mm"
include "coman1.mm"
include "comcom7.mm"
include "coman2.mm"
include "com2an.mm"
include "fh2r.mm"
include "wf.mm"
include "comcom2.mm"
include "ax-a2.mm"
include "anass.mm"
include "anidm.mm"
include "lan.mm"
include "ax-r2.mm"
include "dff.mm"
include "ax-r1.mm"
include "an0.mm"
include "2or.mm"
include "or0.mm"
include "an32.mm"
include "ancom.mm"
include "anor1.mm"

theorem u3lemanb
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->3 b ) ^ b ' ) = ( a ' ^ b ' )

  proof
    wva
    wvb
    wi3
    #
    wvb
    wn
    #
    wa
    wva
    wn
    #
    wvb
    wa
    #
    @2
    @1
    wa
    #
    wo
    #
    wva
    @2
    wvb
    wo
    #
    wa
    #
    wo
    #
    @1
    wa
    #
    @4
    @0
    @8
    @1
    wva
    wvb
    df-i3
    ran
    @9
    @5
    @1
    wa
    #
    @7
    @1
    wa
    #
    wo
    #
    @4
    @5
    @1
    @7
    @1
    @5
    @1
    @3
    @4
    wvb
    @3
    @2
    wvb
    comanr2
    comcom3
    @2
    @1
    comanr2
    com2or
    comcom
    @7
    @5
    @7
    @3
    @4
    @3
    @7
    @3
    wva
    @6
    @3
    wva
    @2
    wvb
    coman1
    #
    comcom7
    @3
    @2
    wvb
    @13
    @2
    wvb
    coman2
    #
    com2or
    com2an
    comcom
    @4
    @7
    @4
    wva
    @6
    @4
    wva
    @2
    @1
    coman1
    #
    comcom7
    @4
    @2
    wvb
    @15
    @4
    wvb
    @2
    @1
    coman2
    comcom7
    com2or
    com2an
    comcom
    com2or
    comcom
    fh2r
    @12
    @4
    wf
    wo
    #
    @4
    @10
    @4
    @11
    wf
    @10
    @3
    @1
    wa
    #
    @4
    @1
    wa
    #
    wo
    #
    @4
    @3
    @1
    @4
    @3
    wvb
    @14
    comcom2
    #
    @3
    @2
    @1
    @13
    @20
    com2an
    fh2r
    @19
    @18
    @17
    wo
    #
    @4
    @17
    @18
    ax-a2
    @21
    @16
    @4
    @18
    @4
    @17
    wf
    @18
    @2
    @1
    @1
    wa
    #
    wa
    @4
    @2
    @1
    @1
    anass
    @22
    @1
    @2
    @1
    anidm
    lan
    ax-r2
    @17
    @2
    wvb
    @1
    wa
    #
    wa
    #
    wf
    @2
    wvb
    @1
    anass
    @24
    @2
    wf
    wa
    #
    wf
    @25
    @24
    wf
    @23
    @2
    wvb
    dff
    lan
    ax-r1
    @2
    an0
    ax-r2
    ax-r2
    2or
    @4
    or0
    #
    ax-r2
    ax-r2
    ax-r2
    @11
    wva
    @1
    wa
    #
    @6
    wa
    #
    wf
    wva
    @6
    @1
    an32
    @28
    @6
    @27
    wa
    #
    wf
    @27
    @6
    ancom
    @29
    @6
    @6
    wn
    #
    wa
    #
    wf
    @27
    @30
    @6
    wva
    wvb
    anor1
    lan
    wf
    @31
    @6
    dff
    ax-r1
    ax-r2
    ax-r2
    ax-r2
    2or
    @26
    ax-r2
    ax-r2
    ax-r2
end
