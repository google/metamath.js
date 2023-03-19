include "wa.mm"
include "wo.mm"
include "ledi.mm"
include "wn.mm"
include "wf.mm"
include "ancom.mm"
include "df-a.mm"
include "2or.mm"
include "ax-r1.mm"
include "con3.mm"
include "ax-r2.mm"
include "con2.mm"
include "2an.mm"
include "anass.mm"
include "comcom2.mm"
include "com3ii.mm"
include "anandi.mm"
include "3tr1.mm"
include "lan.mm"
include "an12.mm"
include "oran.mm"
include "dff.mm"
include "an0.mm"
include "oml3.mm"

theorem fh1
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume fh.1: |- a C b
  assume fh.2: |- a C c


  assert |- ( a ^ ( b v c ) ) = ( ( a ^ b ) v ( a ^ c ) )

  proof
    wva
    wvb
    wa
    #
    wva
    wvc
    wa
    #
    wo
    #
    wva
    wvb
    wvc
    wo
    #
    wa
    #
    @2
    @4
    wva
    wvb
    wvc
    ledi
    @4
    @2
    wn
    #
    wa
    #
    wva
    @3
    wvb
    wn
    #
    wvc
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
    @3
    wva
    wa
    #
    wva
    wn
    #
    @7
    wo
    #
    @13
    @8
    wo
    #
    wa
    #
    wa
    #
    @11
    @4
    @12
    @5
    @16
    wva
    @3
    ancom
    @2
    @16
    @2
    @14
    wn
    #
    @15
    wn
    #
    wo
    #
    @16
    wn
    @0
    @18
    @1
    @19
    wva
    wvb
    df-a
    wva
    wvc
    df-a
    2or
    @20
    @16
    @16
    @20
    wn
    @14
    @15
    df-a
    ax-r1
    con3
    ax-r2
    con2
    2an
    @17
    @3
    wva
    @9
    wa
    #
    wa
    #
    @11
    @17
    @3
    wva
    @16
    wa
    #
    wa
    @22
    @3
    wva
    @16
    anass
    @23
    @21
    @3
    wva
    @14
    wa
    #
    wva
    @15
    wa
    #
    wa
    wva
    @7
    wa
    #
    wva
    @8
    wa
    #
    wa
    @23
    @21
    @24
    @26
    @25
    @27
    wva
    @7
    wva
    wvb
    fh.1
    comcom2
    com3ii
    wva
    @8
    wva
    wvc
    fh.2
    comcom2
    com3ii
    2an
    wva
    @14
    @15
    anandi
    wva
    @7
    @8
    anandi
    3tr1
    lan
    ax-r2
    @3
    wva
    @9
    an12
    ax-r2
    ax-r2
    @11
    wva
    wf
    wa
    wf
    @10
    wf
    wva
    @10
    @3
    @3
    wn
    #
    wa
    #
    wf
    @9
    @28
    @3
    @9
    @3
    @3
    @9
    wn
    wvb
    wvc
    oran
    ax-r1
    con3
    lan
    wf
    @29
    @3
    dff
    ax-r1
    ax-r2
    lan
    wva
    an0
    ax-r2
    ax-r2
    oml3
    ax-r1
end
