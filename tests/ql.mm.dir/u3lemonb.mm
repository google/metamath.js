include "wi3.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "wt.mm"
include "df-i3.mm"
include "ax-r5.mm"
include "or32.mm"
include "ax-a3.mm"
include "lear.mm"
include "df-le2.mm"
include "lor.mm"
include "ax-r2.mm"
include "ancom.mm"
include "2or.mm"
include "comor1.mm"
include "comor2.mm"
include "com2an.mm"
include "comcom2.mm"
include "com2or.mm"
include "comcom7.mm"
include "fh4.mm"
include "ax-a2.mm"
include "df-t.mm"
include "ax-r1.mm"
include "or1.mm"
include "anor1.mm"
include "con2.mm"
include "2an.mm"
include "an1.mm"

theorem u3lemonb
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->3 b ) v b ' ) = 1

  proof
    wva
    wvb
    wi3
    #
    wvb
    wn
    #
    wo
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
    wo
    #
    wt
    @0
    @8
    @1
    wva
    wvb
    df-i3
    ax-r5
    @9
    @5
    @1
    wo
    #
    @7
    wo
    #
    wt
    @5
    @7
    @1
    or32
    @11
    @3
    @1
    wo
    #
    @6
    wva
    wa
    #
    wo
    #
    wt
    @10
    @12
    @7
    @13
    @10
    @3
    @4
    @1
    wo
    #
    wo
    @12
    @3
    @4
    @1
    ax-a3
    @15
    @1
    @3
    @4
    @1
    @2
    @1
    lear
    df-le2
    lor
    ax-r2
    wva
    @6
    ancom
    2or
    @14
    @12
    @6
    wo
    #
    @12
    wva
    wo
    #
    wa
    #
    wt
    @6
    @12
    wva
    @6
    @3
    @1
    @6
    @2
    wvb
    @2
    wvb
    comor1
    #
    @2
    wvb
    comor2
    #
    com2an
    @6
    wvb
    @20
    comcom2
    com2or
    @6
    wva
    @19
    comcom7
    fh4
    @18
    wt
    wt
    wa
    wt
    @16
    wt
    @17
    wt
    @16
    @3
    @1
    @6
    wo
    #
    wo
    #
    wt
    @3
    @1
    @6
    ax-a3
    @22
    @3
    wt
    wo
    wt
    @21
    wt
    @3
    @21
    @6
    @1
    wo
    #
    wt
    @1
    @6
    ax-a2
    @23
    @2
    wvb
    @1
    wo
    #
    wo
    #
    wt
    @2
    wvb
    @1
    ax-a3
    @25
    @2
    wt
    wo
    wt
    @24
    wt
    @2
    wt
    @24
    wvb
    df-t
    ax-r1
    lor
    @2
    or1
    ax-r2
    ax-r2
    ax-r2
    lor
    @3
    or1
    ax-r2
    ax-r2
    @17
    @3
    @1
    wva
    wo
    #
    wo
    #
    wt
    @3
    @1
    wva
    ax-a3
    @27
    @3
    @3
    wn
    #
    wo
    #
    wt
    @26
    @28
    @3
    @28
    @26
    @3
    @26
    @3
    wvb
    @2
    wa
    @26
    wn
    @2
    wvb
    ancom
    wvb
    wva
    anor1
    ax-r2
    con2
    ax-r1
    lor
    wt
    @29
    @3
    df-t
    ax-r1
    ax-r2
    ax-r2
    2an
    wt
    an1
    ax-r2
    ax-r2
    ax-r2
    ax-r2
    ax-r2
end
