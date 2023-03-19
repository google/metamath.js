include "wo.mm"
include "wa.mm"
include "orass.mm"
include "lan.mm"
include "cm.mm"
include "leo.mm"
include "ler.mm"
include "mlduali.mm"
include "tr.mm"
include "leor.mm"
include "ler2an.mm"
include "df2le2.mm"
include "ran.mm"
include "anass.mm"
include "an32.mm"
include "mldual2i.mm"
include "ancom.mm"
include "ror.mm"
include "lea.mm"
include "leror.mm"
include "l42modlem1.mm"
include "orcom.mm"
include "2an.mm"
include "lor.mm"
include "leao1.mm"

theorem testmod2
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d


  assert |- ( ( a v b ) ^ ( a v ( c v d ) ) ) = ( a v ( b ^ ( ( ( a v c ) ^ ( b v d ) ) v ( d ^ ( ( a v c ) v ( ( b v c ) ^ ( d v a ) ) ) ) ) ) )

  proof
    wva
    wvb
    wo
    #
    wva
    wvc
    wvd
    wo
    wo
    #
    wa
    #
    wva
    wvb
    wva
    wvc
    wo
    #
    wvd
    wo
    #
    wa
    #
    wo
    #
    wva
    wvb
    @3
    wvb
    wvd
    wo
    #
    wa
    #
    wvd
    @3
    wvb
    wvc
    wo
    #
    wvd
    wva
    wo
    #
    wa
    #
    wo
    #
    wa
    wo
    #
    wa
    #
    wo
    @2
    @0
    @4
    wa
    #
    @6
    @15
    @2
    @4
    @1
    @0
    wva
    wvc
    wvd
    orass
    lan
    cm
    wva
    wvb
    @4
    wva
    @3
    wvd
    wva
    wvc
    leo
    ler
    mlduali
    tr
    @5
    @14
    wva
    @5
    wvb
    @7
    @3
    wvb
    wo
    #
    wa
    #
    @4
    wa
    #
    wa
    #
    @14
    @5
    wvb
    @17
    wa
    #
    @4
    wa
    #
    @19
    @21
    @5
    @20
    wvb
    @4
    wvb
    @17
    wvb
    @7
    @16
    wvb
    wvd
    leo
    wvb
    @3
    leor
    ler2an
    df2le2
    ran
    cm
    wvb
    @17
    @4
    anass
    tr
    @18
    @13
    wvb
    @18
    @8
    wvd
    wo
    #
    @12
    wa
    #
    @13
    @18
    @22
    @4
    @16
    wa
    #
    wa
    #
    @23
    @18
    @22
    @4
    wa
    #
    @16
    wa
    #
    @25
    @18
    @22
    @16
    wa
    #
    @27
    @18
    @7
    @4
    wa
    #
    @16
    wa
    @28
    @7
    @16
    @4
    an32
    @29
    @22
    @16
    @29
    @7
    @3
    wa
    #
    wvd
    wo
    @22
    wvd
    @3
    @7
    wvd
    wvb
    leor
    mldual2i
    @30
    @8
    wvd
    @7
    @3
    ancom
    ror
    tr
    ran
    tr
    @27
    @28
    @26
    @22
    @16
    @22
    @4
    @8
    @3
    wvd
    @3
    @7
    lea
    leror
    df2le2
    ran
    cm
    tr
    @22
    @4
    @16
    anass
    tr
    @24
    @12
    @22
    @24
    @3
    wva
    wvd
    wo
    #
    wvc
    wvb
    wo
    #
    wa
    #
    wo
    @12
    wva
    wvc
    wvd
    wvb
    l42modlem1
    @33
    @11
    @3
    @33
    @10
    @9
    wa
    @11
    @31
    @10
    @32
    @9
    wva
    wvd
    orcom
    wvc
    wvb
    orcom
    2an
    @10
    @9
    ancom
    tr
    lor
    tr
    lan
    tr
    @8
    wvd
    @12
    @3
    @7
    @11
    leao1
    mlduali
    tr
    lan
    tr
    lor
    tr
end
