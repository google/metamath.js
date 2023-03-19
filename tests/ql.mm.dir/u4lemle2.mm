include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wt.mm"
include "wi4.mm"
include "df-i4.mm"
include "ax-r1.mm"
include "ax-r2.mm"
include "lan.mm"
include "comanr1.mm"
include "comcom6.mm"
include "com2or.mm"
include "comcom.mm"
include "comor1.mm"
include "comcom7.mm"
include "comor2.mm"
include "com2an.mm"
include "comanr2.mm"
include "comcom3.mm"
include "fh2.mm"
include "wf.mm"
include "fh1.mm"
include "anidm.mm"
include "ran.mm"
include "anass.mm"
include "dff.mm"
include "an0.mm"
include "ancom.mm"
include "3tr2.mm"
include "2or.mm"
include "or0.mm"
include "anor1.mm"
include "an12.mm"
include "3tr1.mm"
include "an1.mm"
include "df2le1.mm"

theorem u4lemle2
  param wva: term a
  param wvb: term b
  assume u4lemle2.1: |- ( a ->4 b ) = 1


  assert |- a =< b

  proof
    wva
    wvb
    wva
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
    wa
    #
    wva
    wt
    wa
    @0
    wva
    @7
    wt
    wva
    @7
    wva
    wvb
    wi4
    #
    wt
    @9
    @7
    wva
    wvb
    df-i4
    ax-r1
    u4lemle2.1
    ax-r2
    lan
    @8
    wva
    @3
    wa
    #
    wva
    @6
    wa
    #
    wo
    #
    @0
    @3
    wva
    @6
    wva
    @3
    wva
    @0
    @2
    wva
    wvb
    comanr1
    #
    wva
    @2
    @1
    wvb
    comanr1
    comcom6
    #
    com2or
    comcom
    @3
    @4
    @5
    @4
    @3
    @4
    @0
    @2
    @4
    wva
    wvb
    @4
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
    @4
    @1
    wvb
    @15
    @16
    com2an
    com2or
    comcom
    @5
    @3
    @5
    @0
    @2
    wvb
    @0
    wva
    wvb
    comanr2
    comcom3
    wvb
    @2
    @1
    wvb
    comanr2
    comcom3
    com2or
    comcom
    com2an
    fh2
    @12
    @0
    wf
    wo
    #
    @0
    @10
    @0
    @11
    wf
    @10
    wva
    @0
    wa
    #
    wva
    @2
    wa
    #
    wo
    #
    @0
    wva
    @0
    @2
    @13
    @14
    fh1
    @20
    @17
    @0
    @17
    @20
    @0
    @18
    wf
    @19
    @0
    wva
    wva
    wa
    #
    wvb
    wa
    #
    @18
    @22
    @0
    @21
    wva
    wvb
    wva
    anidm
    ran
    ax-r1
    wva
    wva
    wvb
    anass
    ax-r2
    wf
    wva
    @1
    wa
    #
    wvb
    wa
    #
    @19
    wvb
    wf
    wa
    wvb
    @23
    wa
    wf
    @24
    wf
    @23
    wvb
    wva
    dff
    lan
    wvb
    an0
    wvb
    @23
    ancom
    3tr2
    wva
    @1
    wvb
    anass
    ax-r2
    2or
    ax-r1
    @0
    or0
    #
    ax-r2
    ax-r2
    @4
    wva
    @5
    wa
    #
    wa
    @4
    @4
    wn
    #
    wa
    @11
    wf
    @26
    @27
    @4
    wva
    wvb
    anor1
    lan
    wva
    @4
    @5
    an12
    @4
    dff
    3tr1
    2or
    @25
    ax-r2
    ax-r2
    wva
    an1
    3tr2
    df2le1
end
