include "wi3.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "df-i3.mm"
include "wf.mm"
include "ud3lem3a.mm"
include "ud3lem0c.mm"
include "ax-r2.mm"
include "ud3lem3b.mm"
include "2or.mm"
include "or0.mm"
include "ud3lem3d.mm"
include "coman1.mm"
include "comcom7.mm"
include "coman2.mm"
include "comcom2.mm"
include "com2or.mm"
include "com2an.mm"
include "comcom.mm"
include "comorr.mm"
include "comor1.mm"
include "comor2.mm"
include "comcom3.mm"
include "fh4r.mm"
include "wt.mm"
include "ax-a3.mm"
include "ax-r1.mm"
include "anor2.mm"
include "lor.mm"
include "df-t.mm"
include "ax-r5.mm"
include "or1r.mm"
include "ax-a2.mm"
include "lear.mm"
include "leor.mm"
include "letr.mm"
include "lea.mm"
include "leo.mm"
include "lel2or.mm"
include "df-le2.mm"
include "2an.mm"
include "an1r.mm"
include "or12.mm"
include "df-a.mm"
include "anor1.mm"
include "ax-r4.mm"
include "or1.mm"
include "an1.mm"

theorem ud3lem3
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->3 b ) ->3 ( a v b ) ) = ( a v b )

  proof
    wva
    wvb
    wi3
    #
    wva
    wvb
    wo
    #
    wi3
    @0
    wn
    #
    @1
    wa
    #
    @2
    @1
    wn
    wa
    #
    wo
    #
    @0
    @2
    @1
    wo
    wa
    #
    wo
    #
    @1
    @0
    @1
    df-i3
    @7
    wva
    wvb
    wn
    #
    wo
    #
    @1
    wa
    #
    wva
    wn
    #
    wva
    @8
    wa
    #
    wo
    #
    wa
    #
    @11
    wvb
    wa
    #
    wva
    @11
    wvb
    wo
    #
    wa
    #
    wo
    #
    wo
    #
    @1
    @5
    @14
    @6
    @18
    @5
    @14
    wf
    wo
    @14
    @3
    @14
    @4
    wf
    @3
    @2
    @14
    wva
    wvb
    ud3lem3a
    wva
    wvb
    ud3lem0c
    ax-r2
    wva
    wvb
    ud3lem3b
    2or
    @14
    or0
    ax-r2
    wva
    wvb
    ud3lem3d
    2or
    @19
    @10
    @18
    wo
    #
    @13
    @18
    wo
    #
    wa
    #
    @1
    @10
    @18
    @13
    @10
    @15
    @17
    @15
    @10
    @15
    @9
    @1
    @15
    wva
    @8
    @15
    wva
    @11
    wvb
    coman1
    comcom7
    #
    @15
    wvb
    @11
    wvb
    coman2
    #
    comcom2
    com2or
    @15
    wva
    wvb
    @23
    @24
    com2or
    com2an
    comcom
    @10
    wva
    @16
    wva
    @10
    wva
    @9
    @1
    wva
    @8
    comorr
    #
    wva
    wvb
    comorr
    #
    com2an
    comcom
    @16
    @10
    @16
    @9
    @1
    @16
    wva
    @8
    @16
    wva
    @11
    wvb
    comor1
    comcom7
    #
    @16
    wvb
    @11
    wvb
    comor2
    #
    comcom2
    com2or
    @16
    wva
    wvb
    @27
    @28
    com2or
    com2an
    comcom
    com2an
    com2or
    @10
    @11
    @12
    @11
    @10
    @11
    @9
    @1
    wva
    @9
    @25
    comcom3
    wva
    @1
    @26
    comcom3
    com2an
    comcom
    @12
    @10
    @12
    @9
    @1
    @12
    wva
    @8
    wva
    @8
    coman1
    #
    wva
    @8
    coman2
    #
    com2or
    @12
    wva
    wvb
    @29
    @12
    wvb
    @30
    comcom7
    com2or
    com2an
    comcom
    com2or
    fh4r
    @22
    @1
    wt
    wa
    @1
    @20
    @1
    @21
    wt
    @20
    @9
    @18
    wo
    #
    @1
    @18
    wo
    #
    wa
    #
    @1
    @9
    @18
    @1
    @9
    @15
    @17
    @9
    @11
    wvb
    @9
    wva
    wva
    @8
    comor1
    #
    comcom2
    #
    @9
    wvb
    wva
    @8
    comor2
    comcom7
    #
    com2an
    @9
    wva
    @16
    @34
    @9
    @11
    wvb
    @35
    @36
    com2or
    com2an
    com2or
    @9
    wva
    wvb
    @34
    @36
    com2or
    fh4r
    @33
    wt
    @1
    wa
    @1
    @31
    wt
    @32
    @1
    @31
    @9
    @15
    wo
    #
    @17
    wo
    #
    wt
    @38
    @31
    @9
    @15
    @17
    ax-a3
    ax-r1
    @38
    wt
    @17
    wo
    wt
    @37
    wt
    @17
    @37
    @9
    @9
    wn
    #
    wo
    #
    wt
    @15
    @39
    @9
    wva
    wvb
    anor2
    lor
    wt
    @40
    @9
    df-t
    ax-r1
    ax-r2
    ax-r5
    @17
    or1r
    ax-r2
    ax-r2
    @32
    @18
    @1
    wo
    @1
    @1
    @18
    ax-a2
    @18
    @1
    @15
    @1
    @17
    @15
    wvb
    @1
    @11
    wvb
    lear
    wvb
    wva
    leor
    letr
    @17
    wva
    @1
    wva
    @16
    lea
    wva
    wvb
    leo
    letr
    lel2or
    df-le2
    ax-r2
    2an
    @1
    an1r
    ax-r2
    ax-r2
    @21
    @15
    @13
    @17
    wo
    #
    wo
    #
    wt
    @13
    @15
    @17
    or12
    @42
    @15
    wt
    wo
    wt
    @41
    wt
    @15
    @41
    @13
    @13
    wn
    #
    wo
    #
    wt
    @17
    @43
    @13
    @17
    @11
    @16
    wn
    #
    wo
    #
    wn
    @43
    wva
    @16
    df-a
    @46
    @13
    @45
    @12
    @11
    @12
    @45
    wva
    wvb
    anor1
    ax-r1
    lor
    ax-r4
    ax-r2
    lor
    wt
    @44
    @13
    df-t
    ax-r1
    ax-r2
    lor
    @15
    or1
    ax-r2
    ax-r2
    2an
    @1
    an1
    ax-r2
    ax-r2
    ax-r2
    ax-r2
end
