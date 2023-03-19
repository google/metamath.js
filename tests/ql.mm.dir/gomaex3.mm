include "wo.mm"
include "wn.mm"
include "wa.mm"
include "wi1.mm"
include "df-i1.mm"
include "ax-a2.mm"
include "con2.mm"
include "ud1lem0ab.mm"
include "ax-a1.mm"
include "ax-r2.mm"
include "ax-r4.mm"
include "ran.mm"
include "2or.mm"
include "ax-r1.mm"
include "lan.mm"
include "id.mm"
include "gomaex3lem10.mm"
include "bltr.mm"

theorem gomaex3
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  param wve: term e
  param wvf: term f
  param wvg: term g
  param wvk: term k
  param wvi: term i
  param wvn: term n
  param wvp: term p
  param wvq: term q
  param wvr: term r
  param wvw: term w
  param wvy: term y
  assume gomaex3.1: |- a =< b '
  assume gomaex3.2: |- b =< c '
  assume gomaex3.3: |- c =< d '
  assume gomaex3.5: |- e =< f '
  assume gomaex3.6: |- f =< a '
  assume gomaex3.8: |- ( ( ( i ->2 g ) ^ ( g ->2 y ) ) ^ ( ( ( y ->2 w ) ^ ( w ->2 n ) ) ^ ( ( n ->2 k ) ^ ( k ->2 i ) ) ) ) =< ( g ->2 i )
  assume gomaex3.9: |- p = ( ( a v b ) ->1 ( d v e ) ' ) '
  assume gomaex3.10: |- q = ( ( e v f ) ->1 ( b v c ) ' ) '
  assume gomaex3.11: |- r = ( ( p ' ->1 q ) ' ^ ( c v d ) )
  assume gomaex3.12: |- g = a
  assume gomaex3.14: |- i = c
  assume gomaex3.16: |- k = r
  assume gomaex3.18: |- n = ( p ' ->1 q ) '
  assume gomaex3.20: |- w = q '
  assume gomaex3.22: |- y = ( e v f ) '


  assert |- ( ( ( a v b ) ^ ( d v e ) ' ) ^ ( ( ( ( a v b ) ->1 ( d v e ) ' ) ->1 ( ( e v f ) ->1 ( b v c ) ' ) ' ) ' ->1 ( c v d ) ) ) =< ( ( b v c ) v ( e v f ) ' )

  proof
    wva
    wvb
    wo
    #
    wvd
    wve
    wo
    wn
    #
    wa
    #
    @0
    @1
    wi1
    #
    wve
    wvf
    wo
    #
    wvb
    wvc
    wo
    #
    wn
    wi1
    wn
    #
    wi1
    #
    wn
    #
    wvc
    wvd
    wo
    #
    wi1
    #
    wa
    @2
    wvr
    wvp
    wn
    #
    wvq
    wi1
    #
    wo
    #
    wa
    @5
    @4
    wn
    wo
    @10
    @13
    @2
    @10
    @8
    wn
    #
    @8
    @9
    wa
    #
    wo
    #
    @13
    @8
    @9
    df-i1
    @13
    @16
    @13
    @12
    wvr
    wo
    @16
    wvr
    @12
    ax-a2
    @12
    @14
    wvr
    @15
    @12
    @7
    @14
    @11
    @3
    wvq
    @6
    wvp
    @3
    gomaex3.9
    con2
    gomaex3.10
    ud1lem0ab
    #
    @7
    ax-a1
    ax-r2
    wvr
    @12
    wn
    #
    @9
    wa
    @15
    gomaex3.11
    @18
    @8
    @9
    @12
    @7
    @17
    ax-r4
    ran
    ax-r2
    2or
    ax-r2
    ax-r1
    ax-r2
    lan
    wva
    wvb
    wvc
    wvd
    wve
    wvf
    wvg
    wvb
    @9
    wn
    #
    wvk
    wvi
    @12
    wvn
    wvp
    wvq
    wvr
    @11
    wvq
    wa
    #
    wvw
    wvq
    wvy
    wvf
    gomaex3.1
    gomaex3.2
    gomaex3.3
    gomaex3.5
    gomaex3.6
    gomaex3.8
    gomaex3.9
    gomaex3.10
    gomaex3.11
    gomaex3.12
    wvb
    id
    gomaex3.14
    @19
    id
    gomaex3.16
    @12
    id
    gomaex3.18
    @20
    id
    gomaex3.20
    wvq
    id
    gomaex3.22
    wvf
    id
    gomaex3lem10
    bltr
end
