include "wn.mm"
include "wa.mm"
include "wo.mm"
include "lecon3.mm"
include "lecon.mm"
include "id.mm"
include "wi1.mm"
include "ud1lem0ab.mm"
include "2an.mm"
include "2or.mm"
include "le3tr2.mm"
include "oa4to6dual.mm"
include "oa6fromdual.mm"

theorem oa4to6
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  param wve: term e
  param wvf: term f
  param wvg: term g
  param wvh: term h
  param wvj: term j
  param wvk: term k
  assume oa4to6.oa6.1: |- a =< b '
  assume oa4to6.oa6.2: |- c =< d '
  assume oa4to6.oa6.3: |- e =< f '
  assume oa4to6.4: |- g = ( ( ( a ' ^ b ' ) v ( c ' ^ d ' ) ) v ( e ' ^ f ' ) )
  assume oa4to6.5: |- h = a '
  assume oa4to6.6: |- j = c '
  assume oa4to6.7: |- k = e '
  assume oa4to6.oa4: |- ( ( h ->1 g ) ^ ( h v ( j ^ ( ( ( h ^ j ) v ( ( h ->1 g ) ^ ( j ->1 g ) ) ) v ( ( ( h ^ k ) v ( ( h ->1 g ) ^ ( k ->1 g ) ) ) ^ ( ( j ^ k ) v ( ( j ->1 g ) ^ ( k ->1 g ) ) ) ) ) ) ) ) =< g


  assert |- ( ( ( a v b ) ^ ( c v d ) ) ^ ( e v f ) ) =< ( b v ( a ^ ( c v ( ( ( a v c ) ^ ( b v d ) ) ^ ( ( ( a v e ) ^ ( b v f ) ) v ( ( c v e ) ^ ( d v f ) ) ) ) ) ) )

  proof
    wva
    wvb
    wvc
    wvd
    wve
    wvf
    wva
    wn
    #
    wvb
    wn
    #
    wvc
    wn
    #
    wvd
    wn
    #
    wve
    wn
    #
    wvf
    wn
    #
    @0
    @1
    wa
    @2
    @3
    wa
    wo
    @4
    @5
    wa
    wo
    #
    wvb
    @0
    wva
    wvb
    oa4to6.oa6.1
    lecon3
    lecon
    wvd
    @2
    wvc
    wvd
    oa4to6.oa6.2
    lecon3
    lecon
    wvf
    @4
    wve
    wvf
    oa4to6.oa6.3
    lecon3
    lecon
    @6
    id
    wvh
    wvg
    wi1
    #
    wvh
    wvj
    wvh
    wvj
    wa
    #
    @7
    wvj
    wvg
    wi1
    #
    wa
    #
    wo
    #
    wvh
    wvk
    wa
    #
    @7
    wvk
    wvg
    wi1
    #
    wa
    #
    wo
    #
    wvj
    wvk
    wa
    #
    @9
    @13
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
    wvg
    @0
    @6
    wi1
    #
    @0
    @2
    @0
    @2
    wa
    #
    @23
    @2
    @6
    wi1
    #
    wa
    #
    wo
    #
    @0
    @4
    wa
    #
    @23
    @4
    @6
    wi1
    #
    wa
    #
    wo
    #
    @2
    @4
    wa
    #
    @25
    @29
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
    @6
    oa4to6.oa4
    @7
    @23
    @22
    @38
    wvh
    @0
    wvg
    @6
    oa4to6.5
    oa4to6.4
    ud1lem0ab
    #
    wvh
    @0
    @21
    @37
    oa4to6.5
    wvj
    @2
    @20
    @36
    oa4to6.6
    @11
    @27
    @19
    @35
    @8
    @24
    @10
    @26
    wvh
    @0
    wvj
    @2
    oa4to6.5
    oa4to6.6
    2an
    @7
    @23
    @9
    @25
    @39
    wvj
    @2
    wvg
    @6
    oa4to6.6
    oa4to6.4
    ud1lem0ab
    #
    2an
    2or
    @15
    @31
    @18
    @34
    @12
    @28
    @14
    @30
    wvh
    @0
    wvk
    @4
    oa4to6.5
    oa4to6.7
    2an
    @7
    @23
    @13
    @29
    @39
    wvk
    @4
    wvg
    @6
    oa4to6.7
    oa4to6.4
    ud1lem0ab
    #
    2an
    2or
    @16
    @32
    @17
    @33
    wvj
    @2
    wvk
    @4
    oa4to6.6
    oa4to6.7
    2an
    @9
    @25
    @13
    @29
    @40
    @41
    2an
    2or
    2an
    2or
    2an
    2or
    2an
    oa4to6.4
    le3tr2
    oa4to6dual
    oa6fromdual
end
