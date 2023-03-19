include "cr.mm"
include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "cfz.mm"
include "csgn.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cvv.mm"
include "wceq.mm"
include "signstfv.mm"
include "adantr.mm"
include "simpr.mm"
include "oveq2d.mm"
include "mpteq1d.mm"
include "ovexd.mm"
include "fvmptd.mm"

theorem signstfval
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
  assume signsv.p: |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 } |-> if ( b = 0 , a , b ) )
  assume signsv.w: |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. , <. ( +g ` ndx ) , .+^ >. }
  assume signsv.t: |- T = ( f e. Word RR |-> ( n e. ( 0 ..^ ( # ` f ) ) |-> ( W gsum ( i e. ( 0 ... n ) |-> ( sgn ` ( f ` i ) ) ) ) ) )
  assume signsv.v: |- V = ( f e. Word RR |-> sum_ j e. ( 1 ..^ ( # ` f ) ) if ( ( ( T ` f ) ` j ) =/= ( ( T ` f ) ` ( j - 1 ) ) , 1 , 0 ) )

  disjoint f i
  disjoint f n
  disjoint F f
  disjoint i n
  disjoint F i
  disjoint F n
  disjoint N i
  disjoint N n
  disjoint W f
  disjoint W n
  assert |- ( ( F e. Word RR /\ N e. ( 0 ..^ ( # ` F ) ) ) -> ( ( T ` F ) ` N ) = ( W gsum ( i e. ( 0 ... N ) |-> ( sgn ` ( F ` i ) ) ) ) )

  proof
    cF
    cr
    cword
    wcel
    #
    cN
    cc0
    cF
    chash
    cfv
    cfzo
    co
    #
    wcel
    #
    wa
    #
    vn
    cN
    cW
    vi
    cc0
    vn
    cv
    #
    cfz
    co
    #
    vi
    cv
    cF
    cfv
    csgn
    cfv
    #
    cmpt
    #
    cgsu
    co
    #
    cW
    vi
    cc0
    cN
    cfz
    co
    #
    @6
    cmpt
    #
    cgsu
    co
    @1
    cF
    cT
    cfv
    #
    cvv
    @0
    @11
    vn
    @1
    @8
    cmpt
    wceq
    @2
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
    adantr
    @3
    @4
    cN
    wceq
    #
    wa
    #
    @7
    @10
    cW
    cgsu
    @13
    vi
    @5
    @9
    @6
    @13
    @4
    cN
    cc0
    cfz
    @3
    @12
    simpr
    oveq2d
    mpteq1d
    oveq2d
    @0
    @2
    simpr
    @3
    cW
    @10
    cgsu
    ovexd
    fvmptd
end
