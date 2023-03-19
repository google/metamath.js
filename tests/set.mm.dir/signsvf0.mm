include "c0.mm"
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
include "cr.mm"
include "cword.mm"
include "wcel.mm"
include "wceq.mm"
include "wrd0.mm"
include "signsvvfval.mm"
include "ax-mp.mm"
include "hash0.mm"
include "oveq2i.mm"
include "cle.mm"
include "wbr.mm"
include "0le1.mm"
include "cz.mm"
include "wb.mm"
include "1z.mm"
include "0z.mm"
include "fzon.mm"
include "mp2an.mm"
include "mpbi.mm"
include "eqtri.mm"
include "sumeq1i.mm"
include "sum0.mm"
include "3eqtri.mm"

theorem signsvf0
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
  assert |- ( V ` (/) ) = 0

  proof
    c0
    cV
    cfv
    #
    c1
    c0
    chash
    cfv
    #
    cfzo
    co
    #
    vj
    cv
    #
    c0
    cT
    cfv
    #
    cfv
    @3
    c1
    cmin
    co
    @4
    cfv
    wne
    c1
    cc0
    cif
    #
    vj
    csu
    #
    c0
    @5
    vj
    csu
    cc0
    c0
    cr
    cword
    wcel
    @0
    @6
    wceq
    cr
    wrd0
    c.pd
    cT
    vf
    vi
    vj
    vn
    c0
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signsvvfval
    ax-mp
    @2
    c0
    @5
    vj
    @2
    c1
    cc0
    cfzo
    co
    #
    c0
    @1
    cc0
    c1
    cfzo
    hash0
    oveq2i
    cc0
    c1
    cle
    wbr
    #
    @7
    c0
    wceq
    #
    0le1
    c1
    cz
    wcel
    cc0
    cz
    wcel
    @8
    @9
    wb
    1z
    0z
    c1
    cc0
    fzon
    mp2an
    mpbi
    eqtri
    sumeq1i
    @5
    vj
    sum0
    3eqtri
end
