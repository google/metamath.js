include "cr.mm"
include "cword.mm"
include "wcel.mm"
include "cfv.mm"
include "chash.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wfn.mm"
include "wceq.mm"
include "cv.mm"
include "cfz.mm"
include "csgn.mm"
include "cmpt.mm"
include "cgsu.mm"
include "ovex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "signstfv.mm"
include "fneq1d.mm"
include "mpbiri.mm"
include "hashfn.mm"
include "syl.mm"
include "cn0.mm"
include "lencl.mm"
include "hashfzo0.mm"
include "eqtrd.mm"

theorem signstlen
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
  let cN: class N
  assume signsv.p: |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 } |-> if ( b = 0 , a , b ) )
  assume signsv.w: |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. , <. ( +g ` ndx ) , .+^ >. }
  assume signsv.t: |- T = ( f e. Word RR |-> ( n e. ( 0 ..^ ( # ` f ) ) |-> ( W gsum ( i e. ( 0 ... n ) |-> ( sgn ` ( f ` i ) ) ) ) ) )
  assume signsv.v: |- V = ( f e. Word RR |-> sum_ j e. ( 1 ..^ ( # ` f ) ) if ( ( ( T ` f ) ` j ) =/= ( ( T ` f ) ` ( j - 1 ) ) , 1 , 0 ) )

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
  disjoint N i
  disjoint N n
  assert |- ( F e. Word RR -> ( # ` ( T ` F ) ) = ( # ` F ) )

  proof
    cF
    cr
    cword
    wcel
    #
    cF
    cT
    cfv
    #
    chash
    cfv
    #
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    chash
    cfv
    #
    @3
    @0
    @1
    @4
    wfn
    #
    @2
    @5
    wceq
    @0
    @6
    vn
    @4
    cW
    vi
    cc0
    vn
    cv
    cfz
    co
    vi
    cv
    cF
    cfv
    csgn
    cfv
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    @4
    wfn
    vn
    @4
    @8
    @9
    cW
    @7
    cgsu
    ovex
    @9
    eqid
    fnmpti
    @0
    @4
    @1
    @9
    c.pd
    cT
    vf
    vi
    vj
    vn
    cF
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signstfv
    fneq1d
    mpbiri
    @4
    @1
    hashfn
    syl
    @0
    @3
    cn0
    wcel
    @5
    @3
    wceq
    cr
    cF
    lencl
    @3
    hashfzo0
    syl
    eqtrd
end
