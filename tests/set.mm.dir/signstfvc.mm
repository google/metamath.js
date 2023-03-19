include "cr.mm"
include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "cconcat.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "c0.mm"
include "cs1.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "ccatrid.mm"
include "adantr.mm"
include "simprl.mm"
include "simpll.mm"
include "simplr.mm"
include "s1cld.mm"
include "ccatass.mm"
include "syl3anc.mm"
include "ccatcl.mm"
include "syl2anc.mm"
include "cuz.mm"
include "wss.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "cn0.mm"
include "lencl.mm"
include "syl.mm"
include "nn0zd.mm"
include "caddc.mm"
include "nn0red.mm"
include "nn0addge1.mm"
include "ccatlen.mm"
include "breqtrrd.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "fzoss2.mm"
include "simprr.mm"
include "sseldd.mm"
include "signstfvp.mm"
include "eqtr3d.mm"
include "simpr.mm"
include "eqtrd.mm"
include "exp31.mm"
include "a2d.mm"
include "wrdind.mm"
include "3impib.mm"
include "3com12.mm"

theorem signstfvc
  let c.pd: class .+^
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let ve: setvar e
  let vg: setvar g
  let vk: setvar k
  let cK: class K
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
  disjoint e g
  disjoint e i
  disjoint e k
  disjoint e n
  disjoint F e
  disjoint f g
  disjoint f k
  disjoint g i
  disjoint g k
  disjoint g n
  disjoint F g
  disjoint i k
  disjoint k n
  disjoint F k
  disjoint G g
  disjoint N e
  disjoint N g
  disjoint N k
  disjoint T e
  disjoint T g
  disjoint T k
  disjoint K f
  disjoint K i
  disjoint K n
  assert |- ( ( F e. Word RR /\ G e. Word RR /\ N e. ( 0 ..^ ( # ` F ) ) ) -> ( ( T ` ( F ++ G ) ) ` N ) = ( ( T ` F ) ` N ) )

  proof
    cG
    cr
    cword
    #
    wcel
    #
    cF
    @0
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
    cN
    cF
    cG
    cconcat
    co
    #
    cT
    cfv
    #
    cfv
    #
    cN
    cF
    cT
    cfv
    #
    cfv
    #
    wceq
    #
    @1
    @2
    @5
    @11
    @2
    @5
    wa
    #
    cN
    cF
    vg
    cv
    #
    cconcat
    co
    #
    cT
    cfv
    #
    cfv
    #
    @10
    wceq
    #
    wi
    @12
    cN
    cF
    c0
    cconcat
    co
    #
    cT
    cfv
    #
    cfv
    #
    @10
    wceq
    #
    wi
    @12
    cN
    cF
    ve
    cv
    #
    cconcat
    co
    #
    cT
    cfv
    #
    cfv
    #
    @10
    wceq
    #
    wi
    @12
    cN
    cF
    @22
    vk
    cv
    #
    cs1
    #
    cconcat
    co
    #
    cconcat
    co
    #
    cT
    cfv
    #
    cfv
    #
    @10
    wceq
    #
    wi
    @12
    @11
    wi
    vg
    ve
    vk
    cG
    cr
    @13
    c0
    wceq
    #
    @17
    @21
    @12
    @34
    @16
    @20
    @10
    @34
    cN
    @15
    @19
    @34
    @14
    @18
    cT
    @13
    c0
    cF
    cconcat
    oveq2
    fveq2d
    fveq1d
    eqeq1d
    imbi2d
    @13
    @22
    wceq
    #
    @17
    @26
    @12
    @35
    @16
    @25
    @10
    @35
    cN
    @15
    @24
    @35
    @14
    @23
    cT
    @13
    @22
    cF
    cconcat
    oveq2
    fveq2d
    fveq1d
    eqeq1d
    imbi2d
    @13
    @29
    wceq
    #
    @17
    @33
    @12
    @36
    @16
    @32
    @10
    @36
    cN
    @15
    @31
    @36
    @14
    @30
    cT
    @13
    @29
    cF
    cconcat
    oveq2
    fveq2d
    fveq1d
    eqeq1d
    imbi2d
    @13
    cG
    wceq
    #
    @17
    @11
    @12
    @37
    @16
    @8
    @10
    @37
    cN
    @15
    @7
    @37
    @14
    @6
    cT
    @13
    cG
    cF
    cconcat
    oveq2
    fveq2d
    fveq1d
    eqeq1d
    imbi2d
    @2
    @21
    @5
    @2
    cN
    @19
    @9
    @2
    @18
    cF
    cT
    cr
    cF
    ccatrid
    fveq2d
    fveq1d
    adantr
    @22
    @0
    wcel
    #
    @27
    cr
    wcel
    #
    wa
    #
    @12
    @26
    @33
    @40
    @12
    @26
    @33
    @40
    @12
    wa
    #
    @26
    wa
    @32
    @25
    @10
    @41
    @32
    @25
    wceq
    @26
    @41
    cN
    @23
    @28
    cconcat
    co
    #
    cT
    cfv
    #
    cfv
    #
    @32
    @25
    @41
    cN
    @43
    @31
    @41
    @42
    @30
    cT
    @41
    @2
    @38
    @28
    @0
    wcel
    @42
    @30
    wceq
    @40
    @2
    @5
    simprl
    #
    @38
    @39
    @12
    simpll
    #
    @41
    @27
    cr
    @38
    @39
    @12
    simplr
    #
    s1cld
    cr
    cF
    @22
    @28
    ccatass
    syl3anc
    fveq2d
    fveq1d
    @41
    @23
    @0
    wcel
    #
    @39
    cN
    cc0
    @23
    chash
    cfv
    #
    cfzo
    co
    #
    wcel
    @44
    @25
    wceq
    @41
    @2
    @38
    @48
    @45
    @46
    cr
    cF
    @22
    ccatcl
    syl2anc
    #
    @47
    @41
    @4
    @50
    cN
    @41
    @49
    @3
    cuz
    cfv
    wcel
    #
    @4
    @50
    wss
    @41
    @3
    cz
    wcel
    @49
    cz
    wcel
    @3
    @49
    cle
    wbr
    @52
    @41
    @3
    @41
    @2
    @3
    cn0
    wcel
    @45
    cr
    cF
    lencl
    syl
    #
    nn0zd
    @41
    @49
    @41
    @48
    @49
    cn0
    wcel
    @51
    cr
    @23
    lencl
    syl
    nn0zd
    @41
    @3
    @3
    @22
    chash
    cfv
    #
    caddc
    co
    #
    @49
    cle
    @41
    @3
    cr
    wcel
    @54
    cn0
    wcel
    #
    @3
    @55
    cle
    wbr
    @41
    @3
    @53
    nn0red
    @41
    @38
    @56
    @46
    cr
    @22
    lencl
    syl
    @3
    @54
    nn0addge1
    syl2anc
    @41
    @2
    @38
    @49
    @55
    wceq
    @45
    @46
    cr
    cF
    @22
    ccatlen
    syl2anc
    breqtrrd
    @3
    @49
    eluz2
    syl3anbrc
    @3
    cc0
    @49
    fzoss2
    syl
    @40
    @2
    @5
    simprr
    sseldd
    c.pd
    cT
    vf
    vi
    vj
    vn
    @23
    @27
    cN
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signstfvp
    syl3anc
    eqtr3d
    adantr
    @41
    @26
    simpr
    eqtrd
    exp31
    a2d
    wrdind
    3impib
    3com12
end
