include "wa.mm"
include "wo.mm"
include "wn.mm"
include "comcom.mm"
include "fh4rc.mm"
include "comcom2.mm"
include "2an.mm"
include "an4.mm"
include "an32.mm"
include "comd.mm"
include "lan.mm"
include "fh1r.mm"
include "ran.mm"
include "lea.mm"
include "leo.mm"
include "letr.mm"
include "lecom.mm"
include "coman2.mm"
include "com2or.mm"
include "ancom.mm"
include "cbtr.mm"
include "df2le2.mm"
include "fh1.mm"
include "wf.mm"
include "anass.mm"
include "dff.mm"
include "ax-r1.mm"
include "an0.mm"
include "3tr.mm"
include "lor.mm"
include "or0.mm"
include "ax-r2.mm"
include "2or.mm"
include "ax-a2.mm"
include "lelan.mm"
include "bltr.mm"
include "df-le2.mm"
include "3tr2.mm"
include "df2c1.mm"

theorem gsth
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume gsth.1: |- a C b
  assume gsth.2: |- b C c
  assume gsth.3: |- a C ( b ^ c )


  assert |- ( a ^ b ) C c

  proof
    wva
    wvb
    wa
    #
    wvc
    @0
    wvc
    wo
    #
    @0
    wvc
    wn
    #
    wo
    #
    wa
    #
    @0
    @4
    wva
    wvc
    wo
    #
    wvb
    wvc
    wo
    #
    wa
    #
    wva
    @2
    wo
    #
    wvb
    @2
    wo
    #
    wa
    #
    wa
    @5
    @8
    wa
    #
    @6
    @9
    wa
    #
    wa
    #
    @0
    @1
    @7
    @3
    @10
    wvb
    wvc
    wva
    gsth.2
    wva
    wvb
    gsth.1
    comcom
    #
    fh4rc
    wvb
    @2
    wva
    wvb
    wvc
    gsth.2
    comcom2
    @14
    fh4rc
    2an
    @5
    @6
    @8
    @9
    an4
    @11
    wvb
    wa
    @5
    wvb
    wa
    #
    @8
    wa
    #
    @13
    @0
    @5
    @8
    wvb
    an32
    wvb
    @12
    @11
    wvb
    wvc
    gsth.2
    comd
    lan
    @16
    @0
    wvc
    wvb
    wa
    #
    wo
    #
    @8
    wa
    @0
    @8
    wa
    #
    @17
    @8
    wa
    #
    wo
    #
    @0
    @15
    @18
    @8
    wvb
    wva
    wvc
    @14
    gsth.2
    fh1r
    ran
    @8
    @0
    @17
    @0
    @8
    @0
    @8
    @0
    wva
    @8
    wva
    wvb
    lea
    wva
    @2
    leo
    letr
    #
    lecom
    comcom
    @8
    wvb
    wvc
    wa
    #
    @17
    @23
    @8
    @23
    wva
    @2
    wva
    @23
    gsth.3
    comcom
    #
    @23
    wvc
    wvb
    wvc
    coman2
    comcom2
    #
    com2or
    comcom
    wvb
    wvc
    ancom
    cbtr
    fh1r
    @21
    @0
    @23
    wva
    wa
    #
    wo
    @26
    @0
    wo
    @0
    @19
    @0
    @20
    @26
    @0
    @8
    @22
    df2le2
    @20
    @23
    @8
    wa
    @26
    @23
    @2
    wa
    #
    wo
    #
    @26
    @17
    @23
    @8
    wvc
    wvb
    ancom
    ran
    @23
    wva
    @2
    @24
    @25
    fh1
    @28
    @26
    wf
    wo
    @26
    @27
    wf
    @26
    @27
    wvb
    wvc
    @2
    wa
    #
    wa
    wvb
    wf
    wa
    wf
    wvb
    wvc
    @2
    anass
    @29
    wf
    wvb
    wf
    @29
    wvc
    dff
    ax-r1
    lan
    wvb
    an0
    3tr
    lor
    @26
    or0
    ax-r2
    3tr
    2or
    @0
    @26
    ax-a2
    @26
    @0
    @26
    wva
    @23
    wa
    @0
    @23
    wva
    ancom
    @23
    wvb
    wva
    wvb
    wvc
    lea
    lelan
    bltr
    df-le2
    3tr
    3tr
    3tr2
    3tr
    ax-r1
    df2c1
end
