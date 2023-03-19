include "wo.mm"
include "wn.mm"
include "wa.mm"
include "wi1.mm"
include "gomaex3lem1.mm"
include "lan.mm"
include "gomaex3lem3.mm"
include "wt.mm"
include "ancom.mm"
include "gomaex3lem2.mm"
include "ax-a2.mm"
include "df-t.mm"
include "ax-r1.mm"
include "ax-r2.mm"
include "2an.mm"
include "an1.mm"
include "3tr.mm"
include "gomaex3lem6.mm"
include "bltr.mm"

theorem gomaex3lem7
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
  param wvi: term i
  param wvm: term m
  param wvn: term n
  param wvp: term p
  param wvq: term q
  param wvr: term r
  param wvu: term u
  param wvw: term w
  param wvx: term x
  param wvy: term y
  param wvz: term z
  assume gomaex3lem5.1: |- a =< b '
  assume gomaex3lem5.2: |- b =< c '
  assume gomaex3lem5.3: |- c =< d '
  assume gomaex3lem5.5: |- e =< f '
  assume gomaex3lem5.6: |- f =< a '
  assume gomaex3lem5.8: |- ( ( ( i ->2 g ) ^ ( g ->2 y ) ) ^ ( ( ( y ->2 w ) ^ ( w ->2 n ) ) ^ ( ( n ->2 k ) ^ ( k ->2 i ) ) ) ) =< ( g ->2 i )
  assume gomaex3lem5.9: |- p = ( ( a v b ) ->1 ( d v e ) ' ) '
  assume gomaex3lem5.10: |- q = ( ( e v f ) ->1 ( b v c ) ' ) '
  assume gomaex3lem5.11: |- r = ( ( p ' ->1 q ) ' ^ ( c v d ) )
  assume gomaex3lem5.12: |- g = a
  assume gomaex3lem5.13: |- h = b
  assume gomaex3lem5.14: |- i = c
  assume gomaex3lem5.15: |- j = ( c v d ) '
  assume gomaex3lem5.16: |- k = r
  assume gomaex3lem5.17: |- m = ( p ' ->1 q )
  assume gomaex3lem5.18: |- n = ( p ' ->1 q ) '
  assume gomaex3lem5.19: |- u = ( p ' ^ q )
  assume gomaex3lem5.20: |- w = q '
  assume gomaex3lem5.21: |- x = q
  assume gomaex3lem5.22: |- y = ( e v f ) '
  assume gomaex3lem5.23: |- z = f


  assert |- ( ( ( a v b ) ^ d ' ) ^ ( ( ( r v ( p ' ->1 q ) ) ^ p ' ) ^ e ' ) ) =< ( b v c )

  proof
    wva
    wvb
    wo
    #
    wvd
    wn
    #
    wa
    #
    wvr
    wvp
    wn
    #
    wvq
    wi1
    #
    wo
    #
    @3
    wa
    #
    wve
    wn
    #
    wa
    #
    wa
    #
    @0
    wvc
    wvc
    wvd
    wo
    wn
    wo
    #
    wa
    #
    @5
    @4
    wn
    @3
    wvq
    wa
    wo
    #
    wa
    #
    wvq
    wn
    #
    wvq
    wo
    #
    wve
    wvf
    wo
    wn
    wvf
    wo
    #
    wa
    #
    wa
    #
    wa
    #
    wvb
    wvc
    wo
    @19
    @9
    @11
    @2
    @18
    @8
    @10
    @1
    @0
    wvc
    wvd
    gomaex3lem5.3
    gomaex3lem1
    lan
    @13
    @6
    @17
    @7
    @12
    @3
    @5
    wvp
    wvq
    gomaex3lem3
    lan
    @17
    @16
    @15
    wa
    @7
    wt
    wa
    @7
    @15
    @16
    ancom
    @16
    @7
    @15
    wt
    wve
    wvf
    gomaex3lem5.5
    gomaex3lem2
    @15
    wvq
    @14
    wo
    #
    wt
    @14
    wvq
    ax-a2
    wt
    @20
    wvq
    df-t
    ax-r1
    ax-r2
    2an
    @7
    an1
    3tr
    2an
    2an
    ax-r1
    wva
    wvb
    wvc
    wvd
    wve
    wvf
    wvg
    wvh
    wvj
    wvk
    wvi
    wvm
    wvn
    wvp
    wvq
    wvr
    wvu
    wvw
    wvx
    wvy
    wvz
    gomaex3lem5.1
    gomaex3lem5.2
    gomaex3lem5.3
    gomaex3lem5.5
    gomaex3lem5.6
    gomaex3lem5.8
    gomaex3lem5.9
    gomaex3lem5.10
    gomaex3lem5.11
    gomaex3lem5.12
    gomaex3lem5.13
    gomaex3lem5.14
    gomaex3lem5.15
    gomaex3lem5.16
    gomaex3lem5.17
    gomaex3lem5.18
    gomaex3lem5.19
    gomaex3lem5.20
    gomaex3lem5.21
    gomaex3lem5.22
    gomaex3lem5.23
    gomaex3lem6
    bltr
end
