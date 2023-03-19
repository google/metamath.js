include "cr.mm"
include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cfzo.mm"
include "cres.mm"
include "cin.mm"
include "wfn.mm"
include "wf.mm"
include "signstf.mm"
include "wrdf.mm"
include "ffn.mm"
include "3syl.mm"
include "signstlen.mm"
include "oveq2d.mm"
include "fneq2d.mm"
include "mpbid.mm"
include "fnresin.mm"
include "syl.mm"
include "adantr.mm"
include "wss.mm"
include "wb.mm"
include "cuz.mm"
include "elfzuz3.mm"
include "fzoss2.mm"
include "adantl.mm"
include "incom.mm"
include "wceq.mm"
include "df-ss.mm"
include "biimpi.mm"
include "syl5eqr.mm"
include "wrdres.mm"
include "4syl.mm"
include "wrdfn.mm"
include "fnssres.mm"
include "syl2an.mm"
include "hashfn.mm"
include "cn0.mm"
include "elfznn0.mm"
include "hashfzo0.mm"
include "3eqtrd.mm"
include "cv.mm"
include "cconcat.mm"
include "fvres.mm"
include "ad3antlr.mm"
include "simpr.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "eqtrd.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "ad2antrr.mm"
include "signstfvc.mm"
include "syl3anc.mm"
include "wrex.mm"
include "wrdsplex.mm"
include "r19.29a.mm"
include "eqfnfvd.mm"

theorem signstres
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
  let vg: setvar g
  let vm: setvar m
  let cK: class K
  assume signsv.p: |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 } |-> if ( b = 0 , a , b ) )
  assume signsv.w: |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. , <. ( +g ` ndx ) , .+^ >. }
  assume signsv.t: |- T = ( f e. Word RR |-> ( n e. ( 0 ..^ ( # ` f ) ) |-> ( W gsum ( i e. ( 0 ... n ) |-> ( sgn ` ( f ` i ) ) ) ) ) )
  assume signsv.v: |- V = ( f e. Word RR |-> sum_ j e. ( 1 ..^ ( # ` f ) ) if ( ( ( T ` f ) ` j ) =/= ( ( T ` f ) ` ( j - 1 ) ) , 1 , 0 ) )

  disjoint i n
  disjoint F i
  disjoint F n
  disjoint f i
  disjoint f n
  disjoint N f
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
  disjoint g i
  disjoint g m
  disjoint g n
  disjoint F g
  disjoint i m
  disjoint m n
  disjoint F m
  disjoint f g
  disjoint f m
  disjoint N g
  disjoint N m
  disjoint T g
  disjoint T m
  disjoint K f
  disjoint K i
  disjoint K n
  assert |- ( ( F e. Word RR /\ N e. ( 0 ... ( # ` F ) ) ) -> ( ( T ` F ) |` ( 0 ..^ N ) ) = ( T ` ( F |` ( 0 ..^ N ) ) ) )

  proof
    cF
    cr
    cword
    #
    wcel
    #
    cN
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    wcel
    #
    wa
    #
    vm
    cc0
    cN
    cfzo
    co
    #
    cF
    cT
    cfv
    #
    @5
    cres
    #
    cF
    @5
    cres
    #
    cT
    cfv
    #
    @4
    @7
    cc0
    @2
    cfzo
    co
    #
    @5
    cin
    #
    wfn
    #
    @7
    @5
    wfn
    #
    @1
    @12
    @3
    @1
    @6
    @10
    wfn
    #
    @12
    @1
    @6
    cc0
    @6
    chash
    cfv
    #
    cfzo
    co
    #
    wfn
    #
    @14
    @1
    @6
    @0
    wcel
    @16
    cr
    @6
    wf
    @17
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
    signstf
    cr
    @6
    wrdf
    @16
    cr
    @6
    ffn
    3syl
    @1
    @16
    @10
    @6
    @1
    @15
    @2
    cc0
    cfzo
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
    signstlen
    oveq2d
    fneq2d
    mpbid
    @10
    @5
    @6
    fnresin
    syl
    adantr
    @4
    @5
    @10
    wss
    #
    @12
    @13
    wb
    @3
    @18
    @1
    @3
    @2
    cN
    cuz
    cfv
    wcel
    @18
    cN
    cc0
    @2
    elfzuz3
    cN
    cc0
    @2
    fzoss2
    syl
    #
    adantl
    @18
    @11
    @5
    @7
    @18
    @11
    @5
    @10
    cin
    #
    @5
    @5
    @10
    incom
    @18
    @20
    @5
    wceq
    @5
    @10
    df-ss
    biimpi
    syl5eqr
    fneq2d
    syl
    mpbid
    @4
    @9
    cc0
    @9
    chash
    cfv
    #
    cfzo
    co
    #
    wfn
    #
    @9
    @5
    wfn
    @4
    @8
    @0
    wcel
    #
    @9
    @0
    wcel
    @22
    cr
    @9
    wf
    @23
    cr
    cN
    cF
    wrdres
    #
    c.pd
    cT
    vf
    vi
    vj
    vn
    @8
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signstf
    cr
    @9
    wrdf
    @22
    cr
    @9
    ffn
    4syl
    @4
    @22
    @5
    @9
    @4
    @21
    cN
    cc0
    cfzo
    @4
    @21
    @8
    chash
    cfv
    #
    @5
    chash
    cfv
    #
    cN
    @4
    @24
    @21
    @26
    wceq
    @25
    c.pd
    cT
    vf
    vi
    vj
    vn
    @8
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signstlen
    syl
    @4
    @8
    @5
    wfn
    #
    @26
    @27
    wceq
    @1
    cF
    @10
    wfn
    @18
    @28
    @3
    cr
    cF
    wrdfn
    @19
    @10
    @5
    cF
    fnssres
    syl2an
    @5
    @8
    hashfn
    syl
    #
    @3
    @27
    cN
    wceq
    #
    @1
    @3
    cN
    cn0
    wcel
    @30
    cN
    @2
    elfznn0
    cN
    hashfzo0
    syl
    adantl
    #
    3eqtrd
    oveq2d
    fneq2d
    mpbid
    @4
    vm
    cv
    #
    @5
    wcel
    #
    wa
    #
    cF
    @8
    vg
    cv
    #
    cconcat
    co
    #
    wceq
    #
    @32
    @7
    cfv
    #
    @32
    @9
    cfv
    #
    wceq
    vg
    @0
    @34
    @35
    @0
    wcel
    #
    wa
    #
    @37
    wa
    #
    @38
    @32
    @6
    cfv
    #
    @32
    @36
    cT
    cfv
    #
    cfv
    #
    @39
    @33
    @38
    @43
    wceq
    @4
    @40
    @37
    @32
    @5
    @6
    fvres
    ad3antlr
    @42
    @32
    @6
    @44
    @42
    cF
    @36
    cT
    @41
    @37
    simpr
    fveq2d
    fveq1d
    @42
    @24
    @40
    @32
    cc0
    @26
    cfzo
    co
    #
    wcel
    #
    @45
    @39
    wceq
    @4
    @24
    @33
    @40
    @37
    @25
    ad3antrrr
    @34
    @40
    @37
    simplr
    @34
    @47
    @40
    @37
    @4
    @47
    @33
    @4
    @46
    @5
    @32
    @4
    @26
    cN
    cc0
    cfzo
    @4
    @26
    @27
    cN
    @29
    @31
    eqtrd
    oveq2d
    eleq2d
    biimpar
    ad2antrr
    c.pd
    cT
    vf
    vi
    vj
    vn
    @8
    @35
    @32
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signstfvc
    syl3anc
    3eqtrd
    @4
    @37
    vg
    @0
    wrex
    @33
    vg
    cr
    cN
    cF
    wrdsplex
    adantr
    r19.29a
    eqfnfvd
end
