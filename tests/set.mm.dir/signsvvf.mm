include "cr.mm"
include "cword.mm"
include "cn0.mm"
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
include "wcel.mm"
include "cfn.mm"
include "fzofi.mm"
include "a1i.mm"
include "wa.mm"
include "1nn0.mm"
include "wn.mm"
include "0nn0.mm"
include "ifclda.mm"
include "fsumnn0cl.mm"
include "fmpti.mm"

theorem signsvvf
  let c.pd: class .+^
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let cF: class F
  let cK: class K
  assume signsv.p: |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 } |-> if ( b = 0 , a , b ) )
  assume signsv.w: |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. , <. ( +g ` ndx ) , .+^ >. }
  assume signsv.t: |- T = ( f e. Word RR |-> ( n e. ( 0 ..^ ( # ` f ) ) |-> ( W gsum ( i e. ( 0 ... n ) |-> ( sgn ` ( f ` i ) ) ) ) ) )
  assume signsv.v: |- V = ( f e. Word RR |-> sum_ j e. ( 1 ..^ ( # ` f ) ) if ( ( ( T ` f ) ` j ) =/= ( ( T ` f ) ` ( j - 1 ) ) , 1 , 0 ) )

  disjoint f j
  disjoint T f
  disjoint a b
  disjoint .+^ a
  disjoint .+^ b
  disjoint f i
  disjoint f n
  disjoint i n
  disjoint W f
  disjoint W i
  disjoint W n
  disjoint F f
  disjoint F j
  disjoint F f
  disjoint F i
  disjoint F n
  disjoint K f
  disjoint K i
  disjoint K n
  assert |- V : Word RR --> NN0

  proof
    vf
    cr
    cword
    #
    cn0
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
    @1
    cT
    cfv
    #
    cfv
    @4
    c1
    cmin
    co
    @5
    cfv
    wne
    #
    c1
    cc0
    cif
    #
    vj
    csu
    cV
    signsv.v
    @1
    @0
    wcel
    #
    @3
    @7
    vj
    @3
    cfn
    wcel
    @8
    c1
    @2
    fzofi
    a1i
    @8
    @4
    @3
    wcel
    wa
    #
    @6
    c1
    cc0
    cn0
    c1
    cn0
    wcel
    @9
    @6
    wa
    1nn0
    a1i
    cc0
    cn0
    wcel
    @9
    @6
    wn
    wa
    0nn0
    a1i
    ifclda
    fsumnn0cl
    fmpti
end
