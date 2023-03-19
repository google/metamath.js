include "cr.mm"
include "wcel.mm"
include "cs1.mm"
include "cfv.mm"
include "c1.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "wne.mm"
include "cc0.mm"
include "cif.mm"
include "csu.mm"
include "cword.mm"
include "wceq.mm"
include "s1cl.mm"
include "signsvvfval.mm"
include "syl.mm"
include "c0.mm"
include "s1len.mm"
include "oveq2i.mm"
include "fzo0.mm"
include "eqtri.mm"
include "sumeq1i.mm"
include "sum0.mm"
include "syl6eq.mm"

theorem signsvf1
  let c.pd: class .+^
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cK: class K
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let cF: class F
  assume signsv.p: |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 } |-> if ( b = 0 , a , b ) )
  assume signsv.w: |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. , <. ( +g ` ndx ) , .+^ >. }
  assume signsv.t: |- T = ( f e. Word RR |-> ( n e. ( 0 ..^ ( # ` f ) ) |-> ( W gsum ( i e. ( 0 ... n ) |-> ( sgn ` ( f ` i ) ) ) ) ) )
  assume signsv.v: |- V = ( f e. Word RR |-> sum_ j e. ( 1 ..^ ( # ` f ) ) if ( ( ( T ` f ) ` j ) =/= ( ( T ` f ) ` ( j - 1 ) ) , 1 , 0 ) )

  disjoint f j
  disjoint T f
  disjoint K f
  disjoint K j
  disjoint a b
  disjoint .+^ a
  disjoint .+^ b
  disjoint f i
  disjoint f n
  disjoint i n
  disjoint K f
  disjoint K i
  disjoint K n
  disjoint W f
  disjoint W i
  disjoint W n
  disjoint F f
  disjoint F j
  disjoint F f
  disjoint F i
  disjoint F n
  assert |- ( K e. RR -> ( V ` <" K "> ) = 0 )

  proof
    cK
    cr
    wcel
    #
    cK
    cs1
    #
    cV
    cfv
    #
    c1
    @1
    chash
    cfv
    #
    cfzo
    co
    #
    vj
    cv
    #
    @1
    cT
    cfv
    #
    cfv
    @5
    c1
    cmin
    co
    @6
    cfv
    wne
    c1
    cc0
    cif
    #
    vj
    csu
    #
    cc0
    @0
    @1
    cr
    cword
    wcel
    @2
    @8
    wceq
    cK
    cr
    s1cl
    c.pd
    cT
    vf
    vi
    vj
    vn
    @1
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signsvvfval
    syl
    @8
    c0
    @7
    vj
    csu
    cc0
    @4
    c0
    @7
    vj
    @4
    c1
    c1
    cfzo
    co
    c0
    @3
    c1
    c1
    cfzo
    cK
    s1len
    oveq2i
    c1
    fzo0
    eqtri
    sumeq1i
    @7
    vj
    sum0
    eqtri
    syl6eq
end
