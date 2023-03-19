include "cc0.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "cfz.mm"
include "csgn.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cr.mm"
include "cword.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "wcel.mm"
include "wa.mm"
include "simpl.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "mpteq2dva.mm"
include "mpteq12dv.mm"
include "ovex.mm"
include "mptex.mm"
include "fvmpt.mm"

theorem signstfv
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
  disjoint W f
  assert |- ( F e. Word RR -> ( T ` F ) = ( n e. ( 0 ..^ ( # ` F ) ) |-> ( W gsum ( i e. ( 0 ... n ) |-> ( sgn ` ( F ` i ) ) ) ) ) )

  proof
    vf
    cF
    vn
    cc0
    vf
    cv
    #
    chash
    cfv
    #
    cfzo
    co
    #
    cW
    vi
    cc0
    vn
    cv
    cfz
    co
    #
    vi
    cv
    #
    @0
    cfv
    #
    csgn
    cfv
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    vn
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    cW
    vi
    @3
    @4
    cF
    cfv
    #
    csgn
    cfv
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    cr
    cword
    cT
    @0
    cF
    wceq
    #
    vn
    @2
    @8
    @10
    @14
    @15
    @1
    @9
    cc0
    cfzo
    @0
    cF
    chash
    fveq2
    oveq2d
    @15
    @7
    @13
    cW
    cgsu
    @15
    vi
    @3
    @6
    @12
    @15
    @4
    @3
    wcel
    #
    wa
    #
    @5
    @11
    csgn
    @17
    @4
    @0
    cF
    @15
    @16
    simpl
    fveq1d
    fveq2d
    mpteq2dva
    oveq2d
    mpteq12dv
    signsv.t
    vn
    @10
    @14
    cc0
    @9
    cfzo
    ovex
    mptex
    fvmpt
end
