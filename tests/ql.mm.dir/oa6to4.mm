include "wa.mm"
include "wo.mm"
include "wi1.mm"
include "oa6todual.mm"
include "con1.mm"
include "2an.mm"
include "lor.mm"
include "2or.mm"
include "lan.mm"
include "ancom.mm"
include "u1lemaa.mm"
include "3tr.mm"
include "le3tr2.mm"

theorem oa6to4
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  let wve: term e
  let wvf: term f
  let wvg: term g
  assume oa6to4.1: |- b ' = ( a ->1 g ) '
  assume oa6to4.2: |- d ' = ( c ->1 g ) '
  assume oa6to4.3: |- f ' = ( e ->1 g ) '
  assume oa6to4.oa6: |- ( ( ( a ' v b ' ) ^ ( c ' v d ' ) ) ^ ( e ' v f ' ) ) =< ( b ' v ( a ' ^ ( c ' v ( ( ( a ' v c ' ) ^ ( b ' v d ' ) ) ^ ( ( ( a ' v e ' ) ^ ( b ' v f ' ) ) v ( ( c ' v e ' ) ^ ( d ' v f ' ) ) ) ) ) ) )


  assert |- ( ( a ->1 g ) ^ ( a v ( c ^ ( ( ( a ^ c ) v ( ( a ->1 g ) ^ ( c ->1 g ) ) ) v ( ( ( a ^ e ) v ( ( a ->1 g ) ^ ( e ->1 g ) ) ) ^ ( ( c ^ e ) v ( ( c ->1 g ) ^ ( e ->1 g ) ) ) ) ) ) ) ) =< ( ( ( a ^ g ) v ( c ^ g ) ) v ( e ^ g ) )

  proof
    wvb
    wva
    wvc
    wva
    wvc
    wa
    #
    wvb
    wvd
    wa
    #
    wo
    #
    wva
    wve
    wa
    #
    wvb
    wvf
    wa
    #
    wo
    #
    wvc
    wve
    wa
    #
    wvd
    wvf
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
    #
    wa
    wva
    wvb
    wa
    #
    wvc
    wvd
    wa
    #
    wo
    #
    wve
    wvf
    wa
    #
    wo
    wva
    wvg
    wi1
    #
    wva
    wvc
    @0
    @17
    wvc
    wvg
    wi1
    #
    wa
    #
    wo
    #
    @3
    @17
    wve
    wvg
    wi1
    #
    wa
    #
    wo
    #
    @6
    @18
    @21
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
    #
    wa
    wva
    wvg
    wa
    #
    wvc
    wvg
    wa
    #
    wo
    #
    wve
    wvg
    wa
    #
    wo
    wva
    wvb
    wvc
    wvd
    wve
    wvf
    oa6to4.oa6
    oa6todual
    wvb
    @17
    @12
    @29
    wvb
    @17
    oa6to4.1
    con1
    #
    @11
    @28
    wva
    @10
    @27
    wvc
    @2
    @20
    @9
    @26
    @1
    @19
    @0
    wvb
    @17
    wvd
    @18
    @34
    wvd
    @18
    oa6to4.2
    con1
    #
    2an
    lor
    @5
    @23
    @8
    @25
    @4
    @22
    @3
    wvb
    @17
    wvf
    @21
    @34
    wvf
    @21
    oa6to4.3
    con1
    #
    2an
    lor
    @7
    @24
    @6
    wvd
    @18
    wvf
    @21
    @35
    @36
    2an
    lor
    2an
    2or
    lan
    lor
    2an
    @15
    @32
    @16
    @33
    @13
    @30
    @14
    @31
    @13
    wva
    @17
    wa
    @17
    wva
    wa
    @30
    wvb
    @17
    wva
    @34
    lan
    wva
    @17
    ancom
    wva
    wvg
    u1lemaa
    3tr
    @14
    wvc
    @18
    wa
    @18
    wvc
    wa
    @31
    wvd
    @18
    wvc
    @35
    lan
    wvc
    @18
    ancom
    wvc
    wvg
    u1lemaa
    3tr
    2or
    @16
    wve
    @21
    wa
    @21
    wve
    wa
    @33
    wvf
    @21
    wve
    @36
    lan
    wve
    @21
    ancom
    wve
    wvg
    u1lemaa
    3tr
    2or
    le3tr2
end
