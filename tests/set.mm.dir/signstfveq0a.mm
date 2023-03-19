include "cr.mm"
include "cword.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "cc0.mm"
include "cfv.mm"
include "wne.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "cn.mm"
include "c2.mm"
include "cuz.mm"
include "cn0.mm"
include "simpll.mm"
include "eldifad.mm"
include "chash.mm"
include "lencl.mm"
include "syl5eqel.mm"
include "syl.mm"
include "eldifsn.mm"
include "sylib.mm"
include "hasheq0.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "neeq1i.mm"
include "sylibr.mm"
include "elnnne0.mm"
include "sylanbrc.mm"
include "simplr.mm"
include "simpr.mm"
include "neeqtrrd.mm"
include "necomd.mm"
include "oveq1.mm"
include "1m1e0.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "necon3i.mm"
include "eluz2b3.mm"

theorem signstfveq0a
  let c.pd: class .+^
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cF: class F
  let cN: class N
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let cK: class K
  assume signsv.p: |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 } |-> if ( b = 0 , a , b ) )
  assume signsv.w: |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. , <. ( +g ` ndx ) , .+^ >. }
  assume signsv.t: |- T = ( f e. Word RR |-> ( n e. ( 0 ..^ ( # ` f ) ) |-> ( W gsum ( i e. ( 0 ... n ) |-> ( sgn ` ( f ` i ) ) ) ) ) )
  assume signsv.v: |- V = ( f e. Word RR |-> sum_ j e. ( 1 ..^ ( # ` f ) ) if ( ( ( T ` f ) ` j ) =/= ( ( T ` f ) ` ( j - 1 ) ) , 1 , 0 ) )
  assume signstfveq0.1: |- N = ( # ` F )

  disjoint a b
  disjoint F a
  disjoint F b
  disjoint a f
  disjoint a i
  disjoint a n
  disjoint N a
  disjoint b f
  disjoint b i
  disjoint b n
  disjoint N b
  disjoint f i
  disjoint f n
  disjoint N f
  disjoint i n
  disjoint N i
  disjoint N n
  disjoint T a
  disjoint T b
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
  assert |- ( ( ( F e. ( Word RR \ { (/) } ) /\ ( F ` 0 ) =/= 0 ) /\ ( F ` ( N - 1 ) ) = 0 ) -> N e. ( ZZ>= ` 2 ) )

  proof
    cF
    cr
    cword
    #
    c0
    csn
    #
    cdif
    wcel
    #
    cc0
    cF
    cfv
    #
    cc0
    wne
    #
    wa
    #
    cN
    c1
    cmin
    co
    #
    cF
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    cN
    cn
    wcel
    #
    cN
    c1
    wne
    #
    cN
    c2
    cuz
    cfv
    wcel
    @9
    cN
    cn0
    wcel
    #
    cN
    cc0
    wne
    #
    @10
    @9
    cF
    @0
    wcel
    #
    @12
    @9
    cF
    @0
    @1
    @2
    @4
    @8
    simpll
    #
    eldifad
    @14
    cN
    cF
    chash
    cfv
    #
    cn0
    signstfveq0.1
    cr
    cF
    lencl
    syl5eqel
    syl
    @9
    @14
    cF
    c0
    wne
    #
    wa
    #
    @13
    @9
    @2
    @18
    @15
    cF
    @0
    c0
    eldifsn
    sylib
    @18
    @16
    cc0
    wne
    #
    @13
    @14
    @19
    @17
    @14
    @16
    cc0
    cF
    c0
    cF
    @0
    hasheq0
    necon3bid
    biimpar
    cN
    @16
    cc0
    signstfveq0.1
    neeq1i
    sylibr
    syl
    cN
    elnnne0
    sylanbrc
    @9
    @7
    @3
    wne
    @11
    @9
    @3
    @7
    @9
    @3
    cc0
    @7
    @2
    @4
    @8
    simplr
    @5
    @8
    simpr
    neeqtrrd
    necomd
    cN
    c1
    @7
    @3
    cN
    c1
    wceq
    #
    @6
    cc0
    cF
    @20
    @6
    c1
    c1
    cmin
    co
    cc0
    cN
    c1
    c1
    cmin
    oveq1
    1m1e0
    syl6eq
    fveq2d
    necon3i
    syl
    cN
    eluz2b3
    sylanbrc
end
