include "cr.mm"
include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "w3a.mm"
include "cfz.mm"
include "cv.mm"
include "cs1.mm"
include "cconcat.mm"
include "csgn.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wa.mm"
include "wceq.mm"
include "simp1.mm"
include "adantr.mm"
include "s1cl.mm"
include "3ad2ant2.mm"
include "wss.mm"
include "simp3.mm"
include "fzssfzo.mm"
include "syl.mm"
include "sselda.mm"
include "ccatval1.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "ccatcl.mm"
include "syl2anc.mm"
include "c1.mm"
include "caddc.mm"
include "cz.mm"
include "cuz.mm"
include "lencl.mm"
include "nn0zd.mm"
include "uzid.mm"
include "peano2uz.mm"
include "fzoss2.mm"
include "4syl.mm"
include "3ad2ant1.mm"
include "sseldd.mm"
include "ccatlen.mm"
include "s1len.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "eleqtrrd.mm"
include "signstfval.mm"
include "3eqtr4d.mm"

theorem signstfvp
  let c.pd: class .+^
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  assume signsv.p: |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 } |-> if ( b = 0 , a , b ) )
  assume signsv.w: |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. , <. ( +g ` ndx ) , .+^ >. }
  assume signsv.t: |- T = ( f e. Word RR |-> ( n e. ( 0 ..^ ( # ` f ) ) |-> ( W gsum ( i e. ( 0 ... n ) |-> ( sgn ` ( f ` i ) ) ) ) ) )
  assume signsv.v: |- V = ( f e. Word RR |-> sum_ j e. ( 1 ..^ ( # ` f ) ) if ( ( ( T ` f ) ` j ) =/= ( ( T ` f ) ` ( j - 1 ) ) , 1 , 0 ) )

  disjoint i n
  disjoint N i
  disjoint N n
  disjoint a b
  disjoint .+^ a
  disjoint .+^ b
  disjoint f i
  disjoint f n
  disjoint F f
  disjoint i n
  disjoint F i
  disjoint F n
  disjoint K f
  disjoint K i
  disjoint K n
  disjoint W f
  disjoint W i
  disjoint W n
  assert |- ( ( F e. Word RR /\ K e. RR /\ N e. ( 0 ..^ ( # ` F ) ) ) -> ( ( T ` ( F ++ <" K "> ) ) ` N ) = ( ( T ` F ) ` N ) )

  proof
    cF
    cr
    cword
    #
    wcel
    #
    cK
    cr
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
    w3a
    #
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
    cK
    cs1
    #
    cconcat
    co
    #
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
    cW
    vi
    @7
    @8
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
    cN
    @10
    cT
    cfv
    cfv
    #
    cN
    cF
    cT
    cfv
    cfv
    #
    @6
    @13
    @17
    cW
    cgsu
    @6
    vi
    @7
    @12
    @16
    @6
    @8
    @7
    wcel
    #
    wa
    #
    @11
    @15
    csgn
    @22
    @1
    @9
    @0
    wcel
    #
    @8
    @4
    wcel
    @11
    @15
    wceq
    @6
    @1
    @21
    @1
    @2
    @5
    simp1
    #
    adantr
    @6
    @23
    @21
    @2
    @1
    @23
    @5
    cK
    cr
    s1cl
    3ad2ant2
    #
    adantr
    @6
    @7
    @4
    @8
    @6
    @5
    @7
    @4
    wss
    @1
    @2
    @5
    simp3
    #
    cN
    cc0
    @3
    fzssfzo
    syl
    sselda
    cr
    cF
    @9
    @8
    ccatval1
    syl3anc
    fveq2d
    mpteq2dva
    oveq2d
    @6
    @10
    @0
    wcel
    #
    cN
    cc0
    @10
    chash
    cfv
    #
    cfzo
    co
    #
    wcel
    @19
    @14
    wceq
    @6
    @1
    @23
    @27
    @24
    @25
    cr
    cF
    @9
    ccatcl
    syl2anc
    @6
    cN
    cc0
    @3
    c1
    caddc
    co
    #
    cfzo
    co
    #
    @29
    @6
    @4
    @31
    cN
    @1
    @2
    @4
    @31
    wss
    #
    @5
    @1
    @3
    cz
    wcel
    @3
    @3
    cuz
    cfv
    #
    wcel
    @30
    @33
    wcel
    @32
    @1
    @3
    cr
    cF
    lencl
    nn0zd
    @3
    uzid
    @3
    @3
    peano2uz
    @3
    cc0
    @30
    fzoss2
    4syl
    3ad2ant1
    @26
    sseldd
    @6
    @28
    @30
    cc0
    cfzo
    @6
    @28
    @3
    @9
    chash
    cfv
    #
    caddc
    co
    #
    @30
    @6
    @1
    @23
    @28
    @35
    wceq
    @24
    @25
    cr
    cF
    @9
    ccatlen
    syl2anc
    @34
    c1
    @3
    caddc
    cK
    s1len
    oveq2i
    syl6eq
    oveq2d
    eleqtrrd
    c.pd
    cT
    vf
    vi
    vj
    vn
    @10
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
    syl2anc
    @6
    @1
    @5
    @20
    @18
    wceq
    @24
    @26
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
    syl2anc
    3eqtr4d
end
