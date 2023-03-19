include "wi2.mm"
include "wi4.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wi5.mm"
include "df-i2.mm"
include "ran.mm"
include "u4lemc1.mm"
include "comanr2.mm"
include "comcom6.mm"
include "fh2r.mm"
include "ancom.mm"
include "ax-r2.mm"
include "anass.mm"
include "u4lemanb.mm"
include "lan.mm"
include "ax-r1.mm"
include "anabs.mm"
include "2or.mm"
include "comanr1.mm"
include "fh4r.mm"
include "com2or.mm"
include "fh1.mm"
include "u4lemab.mm"
include "ax-r5.mm"
include "id.mm"
include "leor.mm"
include "df2le2.mm"
include "ax-a3.mm"
include "lear.mm"
include "df-le2.mm"
include "lor.mm"
include "df-i5.mm"

theorem u24lem
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->2 b ) ^ ( a ->4 b ) ) = ( a ->5 b )

  proof
    wva
    wvb
    wi2
    #
    wva
    wvb
    wi4
    #
    wa
    wvb
    wva
    wn
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
    wva
    wvb
    wi5
    #
    @0
    @5
    @1
    wva
    wvb
    df-i2
    ran
    @6
    wvb
    @1
    wa
    #
    @4
    @1
    wa
    #
    wo
    #
    @7
    wvb
    @1
    @4
    wva
    wvb
    u4lemc1
    #
    wvb
    @4
    @2
    @3
    comanr2
    comcom6
    fh2r
    @10
    @8
    @3
    @2
    wa
    #
    wo
    #
    @7
    @8
    @8
    @9
    @12
    @8
    @1
    wvb
    wa
    #
    @8
    wvb
    @1
    ancom
    #
    @1
    wvb
    ancom
    ax-r2
    @9
    @2
    @3
    @1
    wa
    #
    wa
    #
    @12
    @2
    @3
    @1
    anass
    @17
    @2
    @2
    wvb
    wo
    #
    @3
    wa
    #
    wa
    #
    @12
    @16
    @19
    @2
    @16
    @1
    @3
    wa
    @19
    @3
    @1
    ancom
    wva
    wvb
    u4lemanb
    ax-r2
    lan
    @20
    @2
    @18
    wa
    #
    @3
    wa
    #
    @12
    @22
    @20
    @2
    @18
    @3
    anass
    ax-r1
    @22
    @4
    @12
    @21
    @2
    @3
    @2
    wvb
    anabs
    ran
    @2
    @3
    ancom
    ax-r2
    ax-r2
    ax-r2
    ax-r2
    2or
    @13
    wvb
    @12
    wo
    @1
    @12
    wo
    #
    wa
    #
    @7
    wvb
    @12
    @1
    wvb
    @12
    @3
    @2
    comanr1
    comcom6
    #
    @11
    fh4r
    @24
    wvb
    @23
    wa
    #
    @12
    @23
    wa
    #
    wo
    #
    @7
    wvb
    @23
    @12
    wvb
    @1
    @12
    @11
    @25
    com2or
    @25
    fh2r
    @28
    wva
    wvb
    wa
    @2
    wvb
    wa
    wo
    #
    wvb
    @12
    wa
    #
    wo
    #
    @12
    wo
    #
    @7
    @26
    @31
    @27
    @12
    @26
    @8
    @30
    wo
    #
    @31
    wvb
    @1
    @12
    @11
    @25
    fh1
    @33
    @31
    @31
    @8
    @29
    @30
    @8
    @14
    @29
    @15
    wva
    wvb
    u4lemab
    ax-r2
    ax-r5
    @31
    id
    ax-r2
    ax-r2
    @12
    @23
    @12
    @1
    leor
    df2le2
    2or
    @32
    @29
    @30
    @12
    wo
    #
    wo
    #
    @7
    @29
    @30
    @12
    ax-a3
    @35
    @29
    @4
    wo
    #
    @7
    @34
    @4
    @29
    @34
    @12
    @4
    @30
    @12
    wvb
    @12
    lear
    df-le2
    @3
    @2
    ancom
    ax-r2
    lor
    @36
    @7
    @7
    @7
    @36
    wva
    wvb
    df-i5
    ax-r1
    @7
    id
    ax-r2
    ax-r2
    ax-r2
    ax-r2
    ax-r2
    ax-r2
    ax-r2
    ax-r2
    ax-r2
end
