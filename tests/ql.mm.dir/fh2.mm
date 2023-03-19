include "wa.mm"
include "wo.mm"
include "ledi.mm"
include "wn.mm"
include "wf.mm"
include "oran.mm"
include "df-a.mm"
include "con2.mm"
include "ran.mm"
include "ax-r4.mm"
include "ax-r2.mm"
include "lan.mm"
include "an4.mm"
include "comcom.mm"
include "comcom2.mm"
include "com3ii.mm"
include "ancom.mm"
include "ax-a1.mm"
include "ax-r5.mm"
include "comcom3.mm"
include "anass.mm"
include "ax-r1.mm"
include "an12.mm"
include "dff.mm"
include "3tr1.mm"
include "an0.mm"
include "oml3.mm"

theorem fh2
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume fh.1: |- a C b
  assume fh.2: |- a C c


  assert |- ( b ^ ( a v c ) ) = ( ( b ^ a ) v ( b ^ c ) )

  proof
    wvb
    wva
    wa
    #
    wvb
    wvc
    wa
    #
    wo
    #
    wvb
    wva
    wvc
    wo
    #
    wa
    #
    @2
    @4
    wvb
    wva
    wvc
    ledi
    @4
    @2
    wn
    #
    wa
    #
    wva
    wn
    #
    wvc
    wvb
    @1
    wn
    #
    wa
    #
    wa
    #
    wa
    #
    wf
    @6
    @7
    wvc
    wa
    #
    @9
    wa
    #
    @11
    @6
    @7
    @3
    wa
    #
    @9
    wa
    #
    @13
    @6
    @7
    wvb
    wa
    #
    @3
    @8
    wa
    #
    wa
    #
    @15
    @6
    @4
    wvb
    wn
    @7
    wo
    #
    @8
    wa
    #
    wa
    #
    @18
    @5
    @20
    @4
    @2
    @20
    @2
    @0
    wn
    #
    @8
    wa
    #
    wn
    @20
    wn
    @0
    @1
    oran
    @23
    @20
    @22
    @19
    @8
    @0
    @19
    wvb
    wva
    df-a
    con2
    ran
    ax-r4
    ax-r2
    con2
    lan
    @21
    wvb
    @19
    wa
    #
    @17
    wa
    @18
    wvb
    @3
    @19
    @8
    an4
    @24
    @16
    @17
    @24
    wvb
    @7
    wa
    @16
    wvb
    @7
    wvb
    wva
    wva
    wvb
    fh.1
    comcom
    comcom2
    com3ii
    wvb
    @7
    ancom
    ax-r2
    ran
    ax-r2
    ax-r2
    @7
    wvb
    @3
    @8
    an4
    ax-r2
    @14
    @12
    @9
    @14
    @7
    @7
    wn
    #
    wvc
    wo
    #
    wa
    @12
    @3
    @26
    @7
    wva
    @25
    wvc
    wva
    ax-a1
    ax-r5
    lan
    @7
    wvc
    wva
    wvc
    fh.2
    comcom3
    com3ii
    ax-r2
    ran
    ax-r2
    @7
    wvc
    @9
    anass
    ax-r2
    @11
    @7
    wf
    wa
    wf
    @10
    wf
    @7
    wvb
    wvc
    @8
    wa
    wa
    #
    @1
    @8
    wa
    #
    @10
    wf
    @28
    @27
    wvb
    wvc
    @8
    anass
    ax-r1
    wvc
    wvb
    @8
    an12
    @1
    dff
    3tr1
    lan
    @7
    an0
    ax-r2
    ax-r2
    oml3
    ax-r1
end
