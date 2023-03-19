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
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "ctp.mm"
include "cpr.mm"
include "simpll.mm"
include "eldifad.mm"
include "signstcl.mm"
include "sylancom.mm"
include "signstfvneq0.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "tpcomb.mm"
include "difeq1i.mm"
include "wceq.mm"
include "neg1ne0.mm"
include "ax-1ne0.mm"
include "diftpsn3.mm"
include "mp2an.mm"
include "eqtri.mm"
include "syl6eleq.mm"

theorem signstfvcl
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
  let ve: setvar e
  let vk: setvar k
  let vm: setvar m
  let vg: setvar g
  let cK: class K
  assume signsv.p: |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 } |-> if ( b = 0 , a , b ) )
  assume signsv.w: |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. , <. ( +g ` ndx ) , .+^ >. }
  assume signsv.t: |- T = ( f e. Word RR |-> ( n e. ( 0 ..^ ( # ` f ) ) |-> ( W gsum ( i e. ( 0 ... n ) |-> ( sgn ` ( f ` i ) ) ) ) ) )
  assume signsv.v: |- V = ( f e. Word RR |-> sum_ j e. ( 1 ..^ ( # ` f ) ) if ( ( ( T ` f ) ` j ) =/= ( ( T ` f ) ` ( j - 1 ) ) , 1 , 0 ) )

  disjoint i n
  disjoint N i
  disjoint N n
  disjoint f i
  disjoint f n
  disjoint a b
  disjoint a n
  disjoint T a
  disjoint b n
  disjoint T b
  disjoint T n
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
  disjoint e f
  disjoint e i
  disjoint e k
  disjoint e m
  disjoint e n
  disjoint f k
  disjoint f m
  disjoint i k
  disjoint i m
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint g m
  disjoint F g
  disjoint F m
  disjoint N m
  disjoint a e
  disjoint a g
  disjoint a k
  disjoint a m
  disjoint b e
  disjoint b g
  disjoint b k
  disjoint b m
  disjoint e g
  disjoint T e
  disjoint g k
  disjoint g n
  disjoint T g
  disjoint T k
  disjoint T m
  disjoint K f
  disjoint K i
  disjoint K n
  assert |- ( ( ( F e. ( Word RR \ { (/) } ) /\ ( F ` 0 ) =/= 0 ) /\ N e. ( 0 ..^ ( # ` F ) ) ) -> ( ( T ` F ) ` N ) e. { -u 1 , 1 } )

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
    cc0
    wne
    #
    wa
    #
    cN
    cc0
    cF
    chash
    cfv
    cfzo
    co
    wcel
    #
    wa
    #
    cN
    cF
    cT
    cfv
    cfv
    #
    c1
    cneg
    #
    cc0
    c1
    ctp
    #
    cc0
    csn
    #
    cdif
    #
    @8
    c1
    cpr
    #
    @6
    @7
    @9
    wcel
    #
    @7
    cc0
    wne
    @7
    @11
    wcel
    @4
    @5
    cF
    @0
    wcel
    @13
    @6
    cF
    @0
    @1
    @2
    @3
    @5
    simpll
    eldifad
    c.pd
    cT
    vf
    vi
    vj
    vn
    cF
    cN
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signstcl
    sylancom
    c.pd
    cT
    vf
    vi
    vj
    vn
    cF
    cN
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signstfvneq0
    @7
    @9
    cc0
    eldifsn
    sylanbrc
    @11
    @8
    c1
    cc0
    ctp
    #
    @10
    cdif
    #
    @12
    @9
    @14
    @10
    @8
    cc0
    c1
    tpcomb
    difeq1i
    @8
    cc0
    wne
    c1
    cc0
    wne
    @15
    @12
    wceq
    neg1ne0
    ax-1ne0
    @8
    c1
    cc0
    diftpsn3
    mp2an
    eqtri
    syl6eleq
end
