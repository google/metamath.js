include "wa.mm"
include "wi1.mm"
include "wo.mm"
include "wt.mm"
include "wn.mm"
include "an1.mm"
include "1i1.mm"
include "lan.mm"
include "u1lemab.mm"
include "ax-r2.mm"
include "2or.mm"
include "ax-a3.mm"
include "ax-r1.mm"
include "orabs.mm"
include "ax-r5.mm"
include "3tr.mm"
include "2an.mm"
include "lor.mm"
include "or32.mm"
include "leo.mm"
include "le2an.mm"
include "df-le2.mm"
include "ax-a1.mm"
include "df-i1.mm"

theorem oa3-6lem
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( ( a ->1 c ) ^ ( a v ( b ^ ( ( ( a ^ b ) v ( ( a ->1 c ) ^ ( b ->1 c ) ) ) v ( ( ( a ^ 1 ) v ( ( a ->1 c ) ^ ( 1 ->1 c ) ) ) ^ ( ( b ^ 1 ) v ( ( b ->1 c ) ^ ( 1 ->1 c ) ) ) ) ) ) ) ) = ( ( a ->1 c ) ^ ( a v ( b ^ ( ( ( a ' ->1 c ) ^ ( b ' ->1 c ) ) v ( ( a ->1 c ) ^ ( b ->1 c ) ) ) ) ) )

  proof
    wva
    wvb
    wva
    wvb
    wa
    #
    wva
    wvc
    wi1
    #
    wvb
    wvc
    wi1
    #
    wa
    #
    wo
    #
    wva
    wt
    wa
    #
    @1
    wt
    wvc
    wi1
    #
    wa
    #
    wo
    #
    wvb
    wt
    wa
    #
    @2
    @6
    wa
    #
    wo
    #
    wa
    #
    wo
    #
    wa
    #
    wo
    wva
    wvb
    wva
    wn
    #
    wvc
    wi1
    #
    wvb
    wn
    #
    wvc
    wi1
    #
    wa
    #
    @3
    wo
    #
    wa
    #
    wo
    @1
    @14
    @21
    wva
    @13
    @20
    wvb
    @13
    @4
    wva
    @15
    wvc
    wa
    #
    wo
    #
    wvb
    @17
    wvc
    wa
    #
    wo
    #
    wa
    #
    wo
    @0
    @26
    wo
    #
    @3
    wo
    @20
    @12
    @26
    @4
    @8
    @23
    @11
    @25
    @8
    wva
    wva
    wvc
    wa
    #
    @22
    wo
    #
    wo
    #
    wva
    @28
    wo
    #
    @22
    wo
    #
    @23
    @5
    wva
    @7
    @29
    wva
    an1
    @7
    @1
    wvc
    wa
    @29
    @6
    wvc
    @1
    wvc
    1i1
    #
    lan
    wva
    wvc
    u1lemab
    ax-r2
    2or
    @32
    @30
    wva
    @28
    @22
    ax-a3
    ax-r1
    @31
    wva
    @22
    wva
    wvc
    orabs
    ax-r5
    3tr
    @11
    wvb
    wvb
    wvc
    wa
    #
    @24
    wo
    #
    wo
    #
    wvb
    @34
    wo
    #
    @24
    wo
    #
    @25
    @9
    wvb
    @10
    @35
    wvb
    an1
    @10
    @2
    wvc
    wa
    @35
    @6
    wvc
    @2
    @33
    lan
    wvb
    wvc
    u1lemab
    ax-r2
    2or
    @38
    @36
    wvb
    @34
    @24
    ax-a3
    ax-r1
    @37
    wvb
    @24
    wvb
    wvc
    orabs
    ax-r5
    3tr
    2an
    lor
    @0
    @3
    @26
    or32
    @27
    @19
    @3
    @27
    @26
    @19
    @0
    @26
    wva
    @23
    wvb
    @25
    wva
    @22
    leo
    wvb
    @24
    leo
    le2an
    df-le2
    @23
    @16
    @25
    @18
    @23
    @15
    wn
    #
    @22
    wo
    #
    @16
    wva
    @39
    @22
    wva
    ax-a1
    ax-r5
    @16
    @40
    @15
    wvc
    df-i1
    ax-r1
    ax-r2
    @25
    @17
    wn
    #
    @24
    wo
    #
    @18
    wvb
    @41
    @24
    wvb
    ax-a1
    ax-r5
    @18
    @42
    @17
    wvc
    df-i1
    ax-r1
    ax-r2
    2an
    ax-r2
    ax-r5
    3tr
    lan
    lor
    lan
end
