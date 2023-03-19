include "gomaex3h1.mm"
include "gomaex3h2.mm"
include "gomaex3h3.mm"
include "gomaex3h4.mm"
include "gomaex3h5.mm"
include "gomaex3h6.mm"
include "gomaex3h7.mm"
include "gomaex3h8.mm"
include "gomaex3h9.mm"
include "gomaex3h10.mm"
include "gomaex3h11.mm"
include "gomaex3h12.mm"
include "go2n6.mm"

theorem gomaex3lem5
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


  assert |- ( ( ( g v h ) ^ ( i v j ) ) ^ ( ( ( k v m ) ^ ( n v u ) ) ^ ( ( w v x ) ^ ( y v z ) ) ) ) =< ( h v i )

  proof
    wvg
    wvh
    wvj
    wvk
    wvi
    wvm
    wvn
    wvu
    wvw
    wvx
    wvy
    wvz
    wva
    wvb
    wvg
    wvh
    gomaex3lem5.1
    gomaex3lem5.12
    gomaex3lem5.13
    gomaex3h1
    wvb
    wvc
    wvh
    wvi
    gomaex3lem5.2
    gomaex3lem5.13
    gomaex3lem5.14
    gomaex3h2
    wvc
    wvd
    wvj
    wvi
    gomaex3lem5.14
    gomaex3lem5.15
    gomaex3h3
    wvc
    wvd
    wvj
    wvk
    wvp
    wvq
    wvr
    gomaex3lem5.11
    gomaex3lem5.15
    gomaex3lem5.16
    gomaex3h4
    wvc
    wvd
    wvk
    wvm
    wvp
    wvq
    wvr
    gomaex3lem5.11
    gomaex3lem5.16
    gomaex3lem5.17
    gomaex3h5
    wvm
    wvn
    wvp
    wvq
    gomaex3lem5.17
    gomaex3lem5.18
    gomaex3h6
    wvn
    wvp
    wvq
    wvu
    gomaex3lem5.18
    gomaex3lem5.19
    gomaex3h7
    wvp
    wvq
    wvu
    wvw
    gomaex3lem5.19
    gomaex3lem5.20
    gomaex3h8
    wvq
    wvw
    wvx
    gomaex3lem5.20
    gomaex3lem5.21
    gomaex3h9
    wvb
    wvc
    wve
    wvf
    wvq
    wvx
    wvy
    gomaex3lem5.10
    gomaex3lem5.21
    gomaex3lem5.22
    gomaex3h10
    wve
    wvf
    wvy
    wvz
    gomaex3lem5.22
    gomaex3lem5.23
    gomaex3h11
    wva
    wvf
    wvg
    wvz
    gomaex3lem5.6
    gomaex3lem5.12
    gomaex3lem5.23
    gomaex3h12
    gomaex3lem5.8
    go2n6
end
