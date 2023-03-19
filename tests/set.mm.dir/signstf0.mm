include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cs1.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "cv.mm"
include "cfz.mm"
include "csgn.mm"
include "cmpt.mm"
include "cgsu.mm"
include "csn.mm"
include "wceq.mm"
include "c1.mm"
include "s1len.mm"
include "oveq2i.mm"
include "fzo01.mm"
include "eqtri.mm"
include "a1i.mm"
include "wa.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "velsn.mm"
include "sylib.mm"
include "oveq2.mm"
include "cz.mm"
include "0z.mm"
include "fzsn.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "mpteq1d.mm"
include "oveq2d.mm"
include "adantl.mm"
include "cmnd.mm"
include "cneg.mm"
include "ctp.mm"
include "signswmnd.mm"
include "0re.mm"
include "cxr.mm"
include "s1fv.mm"
include "id.mm"
include "eqeltrd.mm"
include "rexrd.mm"
include "sgncl.mm"
include "syl.mm"
include "signswbase.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "gsumsn.mm"
include "syl3anc.mm"
include "adantr.mm"
include "3eqtrd.mm"
include "syldan.mm"
include "mpteq12dva.mm"
include "cword.mm"
include "s1cl.mm"
include "signstfv.mm"
include "cop.mm"
include "sgnclre.mm"
include "s1val.mm"
include "fmptsn.mm"
include "sylancr.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"

theorem signstf0
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
  disjoint i n
  disjoint W f
  disjoint W i
  disjoint W n
  disjoint K f
  disjoint K i
  disjoint K n
  disjoint F f
  disjoint F i
  disjoint F n
  disjoint N i
  disjoint N n
  assert |- ( K e. RR -> ( T ` <" K "> ) = <" ( sgn ` K ) "> )

  proof
    cK
    cr
    wcel
    #
    vn
    cc0
    cK
    cs1
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
    #
    cfz
    co
    #
    vi
    cv
    #
    @1
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
    #
    vn
    cc0
    csn
    #
    cK
    csgn
    cfv
    #
    cmpt
    #
    @1
    cT
    cfv
    #
    @13
    cs1
    #
    @0
    vn
    @3
    @10
    @12
    @13
    @3
    @12
    wceq
    @0
    @3
    cc0
    c1
    cfzo
    co
    @12
    @2
    c1
    cc0
    cfzo
    cK
    s1len
    oveq2i
    fzo01
    eqtri
    #
    a1i
    @0
    @4
    @3
    wcel
    #
    @4
    cc0
    wceq
    #
    @10
    @13
    wceq
    @0
    @18
    wa
    #
    @4
    @12
    wcel
    @19
    @20
    @4
    @3
    @12
    @0
    @18
    simpr
    @17
    syl6eleq
    vn
    cc0
    velsn
    sylib
    @0
    @19
    wa
    @10
    cW
    vi
    @12
    @8
    cmpt
    #
    cgsu
    co
    #
    cc0
    @1
    cfv
    #
    csgn
    cfv
    #
    @13
    @19
    @10
    @22
    wceq
    @0
    @19
    @9
    @21
    cW
    cgsu
    @19
    vi
    @5
    @12
    @8
    @19
    @5
    cc0
    cc0
    cfz
    co
    #
    @12
    @4
    cc0
    cc0
    cfz
    oveq2
    cc0
    cz
    wcel
    @25
    @12
    wceq
    0z
    cc0
    fzsn
    ax-mp
    syl6eq
    mpteq1d
    oveq2d
    adantl
    @0
    @22
    @24
    wceq
    #
    @19
    @0
    cW
    cmnd
    wcel
    #
    cc0
    cr
    wcel
    #
    @24
    c1
    cneg
    cc0
    c1
    ctp
    #
    wcel
    #
    @26
    @27
    @0
    c.pd
    cW
    va
    vb
    signsv.p
    signsv.w
    signswmnd
    a1i
    @28
    @0
    0re
    a1i
    @0
    @23
    cxr
    wcel
    @30
    @0
    @23
    @0
    @23
    cK
    cr
    cK
    cr
    s1fv
    #
    @0
    id
    eqeltrd
    rexrd
    @23
    sgncl
    syl
    @8
    @29
    @24
    vi
    cW
    cc0
    cr
    c.pd
    cW
    va
    vb
    signsv.p
    signsv.w
    signswbase
    @6
    cc0
    wceq
    @7
    @23
    csgn
    @6
    cc0
    @1
    fveq2
    fveq2d
    gsumsn
    syl3anc
    adantr
    @0
    @24
    @13
    wceq
    @19
    @0
    @23
    cK
    csgn
    @31
    fveq2d
    adantr
    3eqtrd
    syldan
    mpteq12dva
    @0
    @1
    cr
    cword
    wcel
    @15
    @11
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
    signstfv
    syl
    @0
    @16
    cc0
    @13
    cop
    csn
    #
    @14
    @0
    @13
    cr
    wcel
    #
    @16
    @32
    wceq
    cK
    sgnclre
    #
    @13
    cr
    s1val
    syl
    @0
    @28
    @33
    @32
    @14
    wceq
    0re
    @34
    vn
    cc0
    @13
    cr
    cr
    fmptsn
    sylancr
    eqtrd
    3eqtr4d
end
