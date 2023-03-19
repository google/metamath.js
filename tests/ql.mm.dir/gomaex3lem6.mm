include "wo.mm"
include "wa.mm"
include "wn.mm"
include "wi1.mm"
include "gomaex3lem5.mm"
include "2or.mm"
include "2an.mm"
include "le3tr2.mm"

theorem gomaex3lem6
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  let wve: term e
  let wvf: term f
  let wvg: term g
  let wvh: term h
  let wvj: term j
  let wvk: term k
  let wvi: term i
  let wvm: term m
  let wvn: term n
  let wvp: term p
  let wvq: term q
  let wvr: term r
  let wvu: term u
  let wvw: term w
  let wvx: term x
  let wvy: term y
  let wvz: term z
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


  assert |- ( ( ( a v b ) ^ ( c v ( c v d ) ' ) ) ^ ( ( ( r v ( p ' ->1 q ) ) ^ ( ( p ' ->1 q ) ' v ( p ' ^ q ) ) ) ^ ( ( q ' v q ) ^ ( ( e v f ) ' v f ) ) ) ) =< ( b v c )

  proof
    wvg
    wvh
    wo
    #
    wvi
    wvj
    wo
    #
    wa
    #
    wvk
    wvm
    wo
    #
    wvn
    wvu
    wo
    #
    wa
    #
    wvw
    wvx
    wo
    #
    wvy
    wvz
    wo
    #
    wa
    #
    wa
    #
    wa
    wvh
    wvi
    wo
    wva
    wvb
    wo
    #
    wvc
    wvc
    wvd
    wo
    wn
    #
    wo
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
    @15
    wn
    #
    @14
    wvq
    wa
    #
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
    #
    wvf
    wo
    #
    wa
    #
    wa
    #
    wa
    wvb
    wvc
    wo
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
    gomaex3lem5
    @2
    @13
    @9
    @26
    @0
    @10
    @1
    @12
    wvg
    wva
    wvh
    wvb
    gomaex3lem5.12
    gomaex3lem5.13
    2or
    wvi
    wvc
    wvj
    @11
    gomaex3lem5.14
    gomaex3lem5.15
    2or
    2an
    @5
    @20
    @8
    @25
    @3
    @16
    @4
    @19
    wvk
    wvr
    wvm
    @15
    gomaex3lem5.16
    gomaex3lem5.17
    2or
    wvn
    @17
    wvu
    @18
    gomaex3lem5.18
    gomaex3lem5.19
    2or
    2an
    @6
    @22
    @7
    @24
    wvw
    @21
    wvx
    wvq
    gomaex3lem5.20
    gomaex3lem5.21
    2or
    wvy
    @23
    wvz
    wvf
    gomaex3lem5.22
    gomaex3lem5.23
    2or
    2an
    2an
    2an
    wvh
    wvb
    wvi
    wvc
    gomaex3lem5.13
    gomaex3lem5.14
    2or
    le3tr2
end
