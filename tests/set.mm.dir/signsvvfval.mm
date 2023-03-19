include "c1.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "cmin.mm"
include "wne.mm"
include "cc0.mm"
include "cif.mm"
include "csu.mm"
include "cr.mm"
include "cword.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "wcel.mm"
include "fveq1d.mm"
include "neeq12d.mm"
include "ifbid.mm"
include "adantr.mm"
include "sumeq12dv.mm"
include "sumex.mm"
include "fvmpt.mm"

theorem signsvvfval
  let c.pd: class .+^
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cF: class F
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let cK: class K
  assume signsv.p: |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 } |-> if ( b = 0 , a , b ) )
  assume signsv.w: |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. , <. ( +g ` ndx ) , .+^ >. }
  assume signsv.t: |- T = ( f e. Word RR |-> ( n e. ( 0 ..^ ( # ` f ) ) |-> ( W gsum ( i e. ( 0 ... n ) |-> ( sgn ` ( f ` i ) ) ) ) ) )
  assume signsv.v: |- V = ( f e. Word RR |-> sum_ j e. ( 1 ..^ ( # ` f ) ) if ( ( ( T ` f ) ` j ) =/= ( ( T ` f ) ` ( j - 1 ) ) , 1 , 0 ) )

  disjoint f j
  disjoint F f
  disjoint F j
  disjoint T f
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
  assert |- ( F e. Word RR -> ( V ` F ) = sum_ j e. ( 1 ..^ ( # ` F ) ) if ( ( ( T ` F ) ` j ) =/= ( ( T ` F ) ` ( j - 1 ) ) , 1 , 0 ) )

  proof
    vf
    cF
    c1
    vf
    cv
    #
    chash
    cfv
    #
    cfzo
    co
    #
    vj
    cv
    #
    @0
    cT
    cfv
    #
    cfv
    #
    @3
    c1
    cmin
    co
    #
    @4
    cfv
    #
    wne
    #
    c1
    cc0
    cif
    #
    vj
    csu
    c1
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    @3
    cF
    cT
    cfv
    #
    cfv
    #
    @6
    @12
    cfv
    #
    wne
    #
    c1
    cc0
    cif
    #
    vj
    csu
    cr
    cword
    cV
    @0
    cF
    wceq
    #
    @2
    @11
    @9
    @16
    vj
    @17
    @1
    @10
    c1
    cfzo
    @0
    cF
    chash
    fveq2
    oveq2d
    @17
    @9
    @16
    wceq
    @3
    @2
    wcel
    @17
    @8
    @15
    c1
    cc0
    @17
    @5
    @13
    @7
    @14
    @17
    @3
    @4
    @12
    @0
    cF
    cT
    fveq2
    #
    fveq1d
    @17
    @6
    @4
    @12
    @18
    fveq1d
    neeq12d
    ifbid
    adantr
    sumeq12dv
    signsv.v
    @11
    @16
    vj
    sumex
    fvmpt
end
