include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi2.mm"
include "wi1.mm"
include "lear.mm"
include "an12.mm"
include "lerr.mm"
include "bltr.mm"
include "leid.mm"
include "lel2or.mm"
include "letr.mm"
include "df-i1.mm"
include "lan.mm"
include "ax-r1.mm"
include "coman1.mm"
include "bctr.mm"
include "comcom2.mm"
include "fh2c.mm"
include "df-i2.mm"
include "anor3.mm"
include "2an.mm"
include "wf.mm"
include "comid.mm"
include "comcom3.mm"
include "comanr2.mm"
include "fh1r.mm"
include "dff.mm"
include "anass.mm"
include "anidm.mm"
include "ax-r2.mm"
include "2or.mm"
include "ax-a2.mm"
include "or0.mm"
include "3tr.mm"
include "ran.mm"
include "3tr2.mm"
include "lea.mm"
include "lecom.mm"
include "fh3.mm"
include "coman2.mm"
include "oran.mm"
include "cbtr.mm"
include "com2an.mm"
include "3tr1.mm"
include "le3tr1.mm"

theorem 1oa
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( ( a ->2 b ) ^ ( ( b v c ) ->1 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) =< ( a ->2 c )

  proof
    wva
    wn
    #
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
    wvb
    wvc
    wo
    #
    wo
    #
    @4
    wvb
    @0
    @1
    wa
    #
    wo
    #
    wo
    #
    wa
    #
    @4
    wvc
    @0
    @2
    wa
    #
    wo
    #
    wo
    #
    wa
    #
    @12
    wva
    wvb
    wi2
    #
    @5
    @15
    wva
    wvc
    wi2
    #
    wa
    #
    wi1
    #
    wa
    #
    @16
    @14
    @13
    @12
    @10
    @13
    lear
    @4
    @12
    @12
    @4
    @1
    @11
    wa
    #
    @12
    @0
    @1
    @2
    an12
    #
    @20
    @11
    wvc
    @1
    @11
    lear
    lerr
    #
    bltr
    @12
    leid
    lel2or
    letr
    @19
    @15
    @5
    wn
    #
    @5
    @17
    wa
    #
    wo
    #
    wa
    @15
    @23
    wa
    #
    @15
    @24
    wa
    #
    wo
    #
    @14
    @18
    @25
    @15
    @5
    @17
    df-i1
    lan
    @24
    @15
    @23
    @24
    @15
    @5
    @16
    wa
    #
    wa
    #
    @15
    @30
    @24
    @15
    @5
    @16
    an12
    ax-r1
    @15
    @29
    coman1
    bctr
    @24
    @5
    @5
    @17
    coman1
    comcom2
    fh2c
    @28
    @4
    @5
    @8
    @12
    wa
    #
    wa
    #
    wo
    #
    @14
    @26
    @4
    @27
    @32
    @26
    @8
    @3
    wa
    #
    @4
    @15
    @8
    @23
    @3
    wva
    wvb
    df-i2
    #
    @3
    @23
    wvb
    wvc
    anor3
    ax-r1
    2an
    @8
    @1
    wa
    #
    @2
    wa
    @7
    @2
    wa
    #
    @34
    @4
    @36
    @7
    @2
    @36
    wvb
    @1
    wa
    #
    @7
    @1
    wa
    #
    wo
    wf
    @7
    wo
    #
    @7
    @1
    wvb
    @7
    wvb
    wvb
    wvb
    comid
    comcom3
    @0
    @1
    comanr2
    fh1r
    @38
    wf
    @39
    @7
    wf
    @38
    wvb
    dff
    ax-r1
    @39
    @0
    @1
    @1
    wa
    #
    wa
    @7
    @0
    @1
    @1
    anass
    @41
    @1
    @0
    @1
    anidm
    lan
    ax-r2
    2or
    @40
    @7
    wf
    wo
    @7
    wf
    @7
    ax-a2
    @7
    or0
    ax-r2
    3tr
    ran
    @8
    @1
    @2
    anass
    @0
    @1
    @2
    anass
    #
    3tr2
    ax-r2
    @27
    @5
    @15
    @17
    wa
    #
    wa
    @32
    @15
    @5
    @17
    an12
    @43
    @31
    @5
    @43
    @15
    @15
    wa
    #
    @16
    wa
    #
    @31
    @45
    @43
    @15
    @15
    @16
    anass
    ax-r1
    @44
    @8
    @16
    @12
    @44
    @15
    @8
    @15
    anidm
    @35
    ax-r2
    wva
    wvc
    df-i2
    #
    2an
    ax-r2
    lan
    ax-r2
    2or
    @6
    @4
    @31
    wo
    #
    wa
    @6
    @9
    @13
    wa
    #
    wa
    @33
    @14
    @47
    @48
    @6
    @4
    @8
    @12
    @4
    @37
    @8
    @37
    @4
    @42
    ax-r1
    @37
    @8
    @37
    @7
    wvb
    @7
    @2
    lea
    lerr
    lecom
    bctr
    #
    @4
    @20
    @12
    @21
    @20
    @12
    @22
    lecom
    bctr
    #
    fh3
    lan
    @4
    @5
    @31
    @4
    @3
    wn
    #
    @5
    @4
    @3
    @0
    @3
    coman2
    comcom2
    @5
    @51
    wvb
    wvc
    oran
    ax-r1
    cbtr
    @4
    @8
    @12
    @49
    @50
    com2an
    fh3
    @6
    @9
    @13
    anass
    3tr1
    ax-r2
    3tr
    @46
    le3tr1
end
