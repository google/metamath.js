include "wi4.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "df-i4.mm"
include "u4lemaa.mm"
include "u4lemnaa.mm"
include "2or.mm"
include "u4lemnoa.mm"
include "ran.mm"
include "ancom.mm"
include "lor.mm"
include "comanr1.mm"
include "com2or.mm"
include "comcom3.mm"
include "comorr.mm"
include "com2an.mm"
include "fh4.mm"
include "comor1.mm"
include "comor2.mm"
include "comcom2.mm"
include "lea.mm"
include "lel2or.mm"
include "leo.mm"
include "letr.mm"
include "df-le2.mm"
include "2an.mm"
include "ax-r2.mm"
include "lan.mm"
include "id.mm"

theorem u4lem1
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->4 b ) ->4 a ) = ( ( ( ( a ^ b ) v ( a ^ b ' ) ) v a ' ) ^ ( ( a v b ) ^ ( a v b ' ) ) )

  proof
    wva
    wvb
    wi4
    #
    wva
    wi4
    @0
    wva
    wa
    #
    @0
    wn
    #
    wva
    wa
    #
    wo
    #
    @2
    wva
    wo
    #
    wva
    wn
    #
    wa
    #
    wo
    #
    wva
    wvb
    wa
    #
    wva
    wvb
    wn
    #
    wa
    #
    wo
    #
    @6
    wo
    #
    wva
    wvb
    wo
    #
    wva
    @10
    wo
    #
    wa
    #
    wa
    #
    @0
    wva
    df-i4
    @8
    @12
    @16
    @6
    wa
    #
    wo
    #
    @17
    @4
    @12
    @7
    @18
    @1
    @9
    @3
    @11
    wva
    wvb
    u4lemaa
    wva
    wvb
    u4lemnaa
    2or
    @5
    @16
    @6
    wva
    wvb
    u4lemnoa
    ran
    2or
    @19
    @12
    @6
    @16
    wa
    #
    wo
    #
    @17
    @18
    @20
    @12
    @16
    @6
    ancom
    lor
    @21
    @13
    @12
    @16
    wo
    #
    wa
    #
    @17
    @6
    @12
    @16
    wva
    @12
    wva
    @9
    @11
    wva
    wvb
    comanr1
    wva
    @10
    comanr1
    com2or
    comcom3
    wva
    @16
    wva
    @14
    @15
    wva
    wvb
    comorr
    wva
    @10
    comorr
    com2an
    comcom3
    fh4
    @23
    @17
    @17
    @22
    @16
    @13
    @22
    @12
    @14
    wo
    #
    @12
    @15
    wo
    #
    wa
    @16
    @14
    @12
    @15
    @14
    @9
    @11
    @14
    wva
    wvb
    wva
    wvb
    comor1
    #
    wva
    wvb
    comor2
    #
    com2an
    @14
    wva
    @10
    @26
    @14
    wvb
    @27
    comcom2
    #
    com2an
    com2or
    @14
    wva
    @10
    @26
    @28
    com2or
    fh4
    @24
    @14
    @25
    @15
    @12
    @14
    @12
    wva
    @14
    @9
    wva
    @11
    wva
    wvb
    lea
    wva
    @10
    lea
    lel2or
    #
    wva
    wvb
    leo
    letr
    df-le2
    @12
    @15
    @12
    wva
    @15
    @29
    wva
    @10
    leo
    letr
    df-le2
    2an
    ax-r2
    lan
    @17
    id
    ax-r2
    ax-r2
    ax-r2
    ax-r2
    ax-r2
end
