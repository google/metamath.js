include "cr.mm"
include "cword.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "c0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cn.mm"
include "signshlen.mm"
include "cn0.mm"
include "lencl.mm"
include "adantr.mm"
include "nn0p1nn.mm"
include "syl.mm"
include "eqeltrd.mm"
include "nnne0d.mm"
include "wceq.mm"
include "wb.mm"
include "signshwrd.mm"
include "hasheq0.mm"
include "necon3bid.mm"
include "mpbid.mm"

theorem signshnz
  let cC: class C
  let c.pd: class .+^
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cF: class F
  let cH: class H
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let cK: class K
  assume signsv.p: |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 } |-> if ( b = 0 , a , b ) )
  assume signsv.w: |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. , <. ( +g ` ndx ) , .+^ >. }
  assume signsv.t: |- T = ( f e. Word RR |-> ( n e. ( 0 ..^ ( # ` f ) ) |-> ( W gsum ( i e. ( 0 ... n ) |-> ( sgn ` ( f ` i ) ) ) ) ) )
  assume signsv.v: |- V = ( f e. Word RR |-> sum_ j e. ( 1 ..^ ( # ` f ) ) if ( ( ( T ` f ) ` j ) =/= ( ( T ` f ) ` ( j - 1 ) ) , 1 , 0 ) )
  assume signs.h: |- H = ( ( <" 0 "> ++ F ) oF - ( ( F ++ <" 0 "> ) oFC x. C ) )

  disjoint a b
  disjoint .+^ a
  disjoint .+^ b
  disjoint f i
  disjoint f n
  disjoint F f
  disjoint i n
  disjoint F i
  disjoint F n
  disjoint W f
  disjoint W i
  disjoint W n
  disjoint K f
  disjoint K i
  disjoint K n
  assert |- ( ( F e. Word RR /\ C e. RR+ ) -> H =/= (/) )

  proof
    cF
    cr
    cword
    #
    wcel
    #
    cC
    crp
    wcel
    #
    wa
    #
    cH
    chash
    cfv
    #
    cc0
    wne
    cH
    c0
    wne
    @3
    @4
    @3
    @4
    cF
    chash
    cfv
    #
    c1
    caddc
    co
    #
    cn
    cC
    c.pd
    cT
    vf
    vi
    vj
    vn
    cF
    cH
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signs.h
    signshlen
    @3
    @5
    cn0
    wcel
    #
    @6
    cn
    wcel
    @1
    @7
    @2
    cr
    cF
    lencl
    adantr
    @5
    nn0p1nn
    syl
    eqeltrd
    nnne0d
    @3
    @4
    cc0
    cH
    c0
    @3
    cH
    @0
    wcel
    @4
    cc0
    wceq
    cH
    c0
    wceq
    wb
    cC
    c.pd
    cT
    vf
    vi
    vj
    vn
    cF
    cH
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signs.h
    signshwrd
    cH
    @0
    hasheq0
    syl
    necon3bid
    mpbid
end
