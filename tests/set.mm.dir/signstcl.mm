include "cr.mm"
include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "wa.mm"
include "cfz.mm"
include "cv.mm"
include "csgn.mm"
include "cmpt.mm"
include "cgsu.mm"
include "c1.mm"
include "cneg.mm"
include "ctp.mm"
include "signstfval.mm"
include "signswbase.mm"
include "cmnd.mm"
include "signswmnd.mm"
include "a1i.mm"
include "cuz.mm"
include "wss.mm"
include "cn0.mm"
include "fzo0ssnn0.mm"
include "nn0uz.mm"
include "sseqtri.mm"
include "sselda.mm"
include "cxr.mm"
include "wf.mm"
include "wrdf.mm"
include "ad2antrr.mm"
include "fzssfzo.mm"
include "adantl.mm"
include "ffvelrnd.mm"
include "rexrd.mm"
include "sgncl.mm"
include "syl.mm"
include "gsumncl.mm"
include "eqeltrd.mm"

theorem signstcl
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

  disjoint a b
  disjoint .+^ a
  disjoint .+^ b
  disjoint f i
  disjoint f n
  disjoint F f
  disjoint i n
  disjoint F i
  disjoint F n
  disjoint N i
  disjoint N n
  disjoint W f
  disjoint W i
  disjoint W n
  assert |- ( ( F e. Word RR /\ N e. ( 0 ..^ ( # ` F ) ) ) -> ( ( T ` F ) ` N ) e. { -u 1 , 0 , 1 } )

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
    #
    cfzo
    co
    #
    wcel
    #
    wa
    #
    cN
    cF
    cT
    cfv
    cfv
    cW
    vi
    cc0
    cN
    cfz
    co
    #
    vi
    cv
    #
    cF
    cfv
    #
    csgn
    cfv
    #
    cmpt
    cgsu
    co
    c1
    cneg
    cc0
    c1
    ctp
    #
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
    signstfval
    @4
    @8
    cN
    vi
    @9
    cW
    cc0
    c.pd
    cW
    va
    vb
    signsv.p
    signsv.w
    signswbase
    cW
    cmnd
    wcel
    @4
    c.pd
    cW
    va
    vb
    signsv.p
    signsv.w
    signswmnd
    a1i
    @0
    @2
    cc0
    cuz
    cfv
    #
    cN
    @2
    @10
    wss
    @0
    @2
    cn0
    @10
    @1
    fzo0ssnn0
    nn0uz
    sseqtri
    a1i
    sselda
    @4
    @6
    @5
    wcel
    #
    wa
    #
    @7
    cxr
    wcel
    @8
    @9
    wcel
    @12
    @7
    @12
    @2
    cr
    @6
    cF
    @0
    @2
    cr
    cF
    wf
    @3
    @11
    cr
    cF
    wrdf
    ad2antrr
    @4
    @5
    @2
    @6
    @3
    @5
    @2
    wss
    @0
    cN
    cc0
    @1
    fzssfzo
    adantl
    sselda
    ffvelrnd
    rexrd
    @7
    sgncl
    syl
    gsumncl
    eqeltrd
end
