include "cr.mm"
include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "cfz.mm"
include "csgn.mm"
include "cmpt.mm"
include "cgsu.mm"
include "signstfv.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "ctp.mm"
include "wss.mm"
include "neg1rr.mm"
include "0re.mm"
include "1re.mm"
include "tpssi.mm"
include "mp3an.mm"
include "signswbase.mm"
include "cmnd.mm"
include "signswmnd.mm"
include "a1i.mm"
include "cuz.mm"
include "cn0.mm"
include "fzo0ssnn0.mm"
include "nn0uz.mm"
include "sseqtri.mm"
include "sselda.mm"
include "cxr.mm"
include "wrdf.mm"
include "ad2antrr.mm"
include "fzssfzo.mm"
include "adantl.mm"
include "ffvelrnd.mm"
include "rexrd.mm"
include "sgncl.mm"
include "syl.mm"
include "gsumncl.mm"
include "sseldi.mm"
include "fmpt3d.mm"
include "iswrdi.mm"

theorem signstf
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
  assert |- ( F e. Word RR -> ( T ` F ) e. Word RR )

  proof
    cF
    cr
    cword
    #
    wcel
    #
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    cr
    cF
    cT
    cfv
    #
    wf
    @4
    @0
    wcel
    @1
    vn
    @3
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
    #
    cr
    @4
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
    @1
    @5
    @3
    wcel
    #
    wa
    #
    c1
    cneg
    #
    cc0
    c1
    ctp
    #
    cr
    @10
    @13
    cr
    wcel
    cc0
    cr
    wcel
    c1
    cr
    wcel
    @14
    cr
    wss
    neg1rr
    0re
    1re
    @13
    cc0
    c1
    cr
    tpssi
    mp3an
    @12
    @9
    @5
    vi
    @14
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
    @12
    c.pd
    cW
    va
    vb
    signsv.p
    signsv.w
    signswmnd
    a1i
    @1
    @3
    cc0
    cuz
    cfv
    #
    @5
    @3
    @15
    wss
    @1
    @3
    cn0
    @15
    @2
    fzo0ssnn0
    nn0uz
    sseqtri
    a1i
    sselda
    @12
    @7
    @6
    wcel
    #
    wa
    #
    @8
    cxr
    wcel
    @9
    @14
    wcel
    @17
    @8
    @17
    @3
    cr
    @7
    cF
    @1
    @3
    cr
    cF
    wf
    @11
    @16
    cr
    cF
    wrdf
    ad2antrr
    @12
    @6
    @3
    @7
    @11
    @6
    @3
    wss
    @1
    @5
    cc0
    @2
    fzssfzo
    adantl
    sselda
    ffvelrnd
    rexrd
    @8
    sgncl
    syl
    gsumncl
    sseldi
    fmpt3d
    cr
    @2
    @4
    iswrdi
    syl
end
