include "wi4.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "df-i4.mm"
include "ran.mm"
include "comanr1.mm"
include "comcom3.mm"
include "com2or.mm"
include "comcom.mm"
include "comor1.mm"
include "comcom7.mm"
include "comor2.mm"
include "com2an.mm"
include "comanr2.mm"
include "fh2r.mm"
include "fh1r.mm"
include "wf.mm"
include "an32.mm"
include "ancom.mm"
include "dff.mm"
include "ax-r1.mm"
include "lan.mm"
include "an0.mm"
include "ax-r2.mm"
include "anidm.mm"
include "2or.mm"
include "ax-a2.mm"
include "or0.mm"
include "leo.mm"
include "df2le2.mm"
include "id.mm"

theorem u4lemana
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->4 b ) ^ a ' ) = ( ( a ' ^ b ) v ( a ' ^ b ' ) )

  proof
    wva
    wvb
    wi4
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
    wo
    #
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
    @1
    @6
    wa
    #
    wo
    #
    @0
    @8
    @1
    wva
    wvb
    df-i4
    ran
    @9
    @4
    @1
    wa
    #
    @7
    @1
    wa
    #
    wo
    #
    @11
    @4
    @1
    @7
    @1
    @4
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
    comcom
    @4
    @5
    @6
    @5
    @4
    @5
    @2
    @3
    @5
    wva
    wvb
    @5
    wva
    @1
    wvb
    comor1
    #
    comcom7
    @1
    wvb
    comor2
    #
    com2an
    @5
    @1
    wvb
    @17
    @18
    com2an
    com2or
    comcom
    @6
    @4
    @6
    @2
    @3
    wvb
    @2
    wva
    wvb
    comanr2
    comcom3
    wvb
    @3
    @1
    wvb
    comanr2
    comcom3
    com2or
    comcom
    com2an
    fh2r
    @14
    @11
    @11
    @12
    @3
    @13
    @10
    @12
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
    @15
    @16
    fh1r
    @21
    wf
    @3
    wo
    #
    @3
    @19
    wf
    @20
    @3
    @19
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
    @24
    wvb
    @23
    wa
    #
    wf
    @23
    wvb
    ancom
    @25
    wvb
    wf
    wa
    wf
    @23
    wf
    wvb
    wf
    @23
    wva
    dff
    ax-r1
    lan
    wvb
    an0
    ax-r2
    ax-r2
    ax-r2
    @20
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
    @26
    @1
    wvb
    @1
    anidm
    ran
    ax-r2
    2or
    @22
    @3
    wf
    wo
    @3
    wf
    @3
    ax-a2
    @3
    or0
    ax-r2
    ax-r2
    ax-r2
    @13
    @5
    @1
    wa
    #
    @6
    wa
    @10
    @5
    @6
    @1
    an32
    @27
    @1
    @6
    @27
    @1
    @5
    wa
    @1
    @5
    @1
    ancom
    @1
    @5
    @1
    wvb
    leo
    df2le2
    ax-r2
    ran
    ax-r2
    2or
    @11
    id
    ax-r2
    ax-r2
    ax-r2
end
