include "cr.mm"
include "cword.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "csgn.mm"
include "wceq.mm"
include "cs1.mm"
include "chash.mm"
include "cfzo.mm"
include "wf.mm"
include "eldifsn.mm"
include "biimpi.mm"
include "adantr.mm"
include "simpld.mm"
include "wrdf.mm"
include "syl.mm"
include "cn.mm"
include "lennncl.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "ffvelrnd.mm"
include "signstf0.mm"
include "simpr.mm"
include "syl5eqr.mm"
include "eqs1.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "oveq1.mm"
include "1m1e0.mm"
include "syl6eq.mm"
include "s1eqd.mm"
include "3eqtr4d.mm"
include "fveq12d.mm"
include "cneg.mm"
include "ctp.mm"
include "cxr.mm"
include "oveq1i.mm"
include "fzo0end.mm"
include "3syl.mm"
include "syl5eqel.mm"
include "rexrd.mm"
include "sgncl.mm"
include "s1fv.mm"
include "eqtrd.mm"
include "cres.mm"
include "cconcat.mm"
include "cop.mm"
include "csubstr.mm"
include "clsw.mm"
include "cfz.mm"
include "fzossfz.mm"
include "sseldi.mm"
include "swrd0val.mm"
include "oveq1d.mm"
include "swrdccatwrd.mm"
include "eqcomd.mm"
include "oveq2i.mm"
include "a1i.mm"
include "reseq2d.mm"
include "lsw.mm"
include "eqtr4d.mm"
include "oveq12d.mm"
include "wfn.mm"
include "wss.mm"
include "ffn.mm"
include "oveq2d.mm"
include "fneq2d.mm"
include "mpbird.mm"
include "cn0.mm"
include "cz.mm"
include "nnnn0d.mm"
include "nn0z.mm"
include "fzossrbm1.mm"
include "fnssres.mm"
include "hashfn.mm"
include "nnm1nn0.mm"
include "hashfzo0.mm"
include "swrdcl.mm"
include "eqeltrrd.mm"
include "nncnd.mm"
include "1cnd.mm"
include "subne0d.mm"
include "eqnetrd.mm"
include "fveq2.mm"
include "hash0.mm"
include "necon3i.mm"
include "jca.mm"
include "signstfvn.mm"
include "signstcl.mm"
include "sgn0bi.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "signswlid.mm"
include "syl21anc.mm"
include "3eqtrd.mm"
include "pm2.61dane.mm"

theorem signsvtn0
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
  let cK: class K
  assume signsv.p: |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 } |-> if ( b = 0 , a , b ) )
  assume signsv.w: |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. , <. ( +g ` ndx ) , .+^ >. }
  assume signsv.t: |- T = ( f e. Word RR |-> ( n e. ( 0 ..^ ( # ` f ) ) |-> ( W gsum ( i e. ( 0 ... n ) |-> ( sgn ` ( f ` i ) ) ) ) ) )
  assume signsv.v: |- V = ( f e. Word RR |-> sum_ j e. ( 1 ..^ ( # ` f ) ) if ( ( ( T ` f ) ` j ) =/= ( ( T ` f ) ` ( j - 1 ) ) , 1 , 0 ) )
  assume signsvtn0.1: |- N = ( # ` F )

  disjoint a b
  disjoint F a
  disjoint F b
  disjoint a f
  disjoint a i
  disjoint a n
  disjoint N a
  disjoint b f
  disjoint b i
  disjoint b n
  disjoint N b
  disjoint f i
  disjoint f n
  disjoint N f
  disjoint i n
  disjoint N i
  disjoint N n
  disjoint T a
  disjoint T b
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
  disjoint K f
  disjoint K i
  disjoint K n
  assert |- ( ( F e. ( Word RR \ { (/) } ) /\ ( F ` ( N - 1 ) ) =/= 0 ) -> ( ( T ` F ) ` ( N - 1 ) ) = ( sgn ` ( F ` ( N - 1 ) ) ) )

  proof
    cF
    cr
    cword
    #
    c0
    csn
    cdif
    #
    wcel
    #
    cN
    c1
    cmin
    co
    #
    cF
    cfv
    #
    cc0
    wne
    #
    wa
    #
    @3
    cF
    cT
    cfv
    #
    cfv
    #
    @4
    csgn
    cfv
    #
    wceq
    cN
    c1
    @6
    cN
    c1
    wceq
    #
    wa
    #
    @8
    cc0
    @9
    cs1
    #
    cfv
    #
    @9
    @11
    @3
    cc0
    @7
    @12
    @11
    cc0
    cF
    cfv
    #
    cs1
    #
    cT
    cfv
    #
    @14
    csgn
    cfv
    #
    cs1
    #
    @7
    @12
    @11
    @14
    cr
    wcel
    @16
    @18
    wceq
    @11
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    cr
    cc0
    cF
    @11
    cF
    @0
    wcel
    #
    @20
    cr
    cF
    wf
    #
    @6
    @21
    @10
    @6
    @21
    cF
    c0
    wne
    #
    @2
    @21
    @23
    wa
    #
    @5
    @2
    @24
    cF
    @0
    c0
    eldifsn
    biimpi
    adantr
    #
    simpld
    #
    adantr
    #
    cr
    cF
    wrdf
    #
    syl
    @11
    @19
    cn
    wcel
    #
    cc0
    @20
    wcel
    @6
    @29
    @10
    @6
    @24
    @29
    @25
    cr
    cF
    lennncl
    #
    syl
    #
    adantr
    @19
    lbfzo0
    sylibr
    ffvelrnd
    c.pd
    cT
    vf
    vi
    vj
    vn
    @14
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signstf0
    syl
    @11
    cF
    @15
    cT
    @11
    @21
    @19
    c1
    wceq
    cF
    @15
    wceq
    @27
    @11
    @19
    cN
    c1
    signsvtn0.1
    @6
    @10
    simpr
    #
    syl5eqr
    cr
    cF
    eqs1
    syl2anc
    fveq2d
    @11
    @10
    @12
    @18
    wceq
    @32
    @10
    @9
    @17
    @10
    @4
    @14
    csgn
    @10
    @3
    cc0
    cF
    @10
    @3
    c1
    c1
    cmin
    co
    cc0
    cN
    c1
    c1
    cmin
    oveq1
    1m1e0
    syl6eq
    #
    fveq2d
    fveq2d
    s1eqd
    syl
    3eqtr4d
    @11
    @10
    @3
    cc0
    wceq
    @32
    @33
    syl
    fveq12d
    @11
    @9
    c1
    cneg
    cc0
    c1
    ctp
    #
    wcel
    #
    @13
    @9
    wceq
    @6
    @35
    @10
    @6
    @4
    cxr
    wcel
    #
    @35
    @6
    @4
    @6
    @20
    cr
    @3
    cF
    @6
    @21
    @22
    @26
    @28
    syl
    @6
    @3
    @19
    c1
    cmin
    co
    #
    @20
    cN
    @19
    c1
    cmin
    signsvtn0.1
    oveq1i
    #
    @6
    @24
    @29
    @37
    @20
    wcel
    @25
    @30
    @19
    fzo0end
    3syl
    #
    syl5eqel
    ffvelrnd
    #
    rexrd
    #
    @4
    sgncl
    syl
    #
    adantr
    @9
    @34
    s1fv
    syl
    eqtrd
    @6
    cN
    c1
    wne
    #
    wa
    #
    @8
    cF
    cc0
    @3
    cfzo
    co
    #
    cres
    #
    chash
    cfv
    #
    @46
    @4
    cs1
    #
    cconcat
    co
    #
    cT
    cfv
    #
    cfv
    #
    @47
    c1
    cmin
    co
    #
    @46
    cT
    cfv
    cfv
    #
    @9
    c.pd
    co
    #
    @9
    @6
    @8
    @51
    wceq
    @43
    @6
    @3
    @47
    @7
    @50
    @6
    cF
    @49
    cT
    @6
    cF
    cc0
    @37
    cop
    csubstr
    co
    #
    cF
    clsw
    cfv
    #
    cs1
    #
    cconcat
    co
    #
    cF
    cc0
    @37
    cfzo
    co
    #
    cres
    #
    @57
    cconcat
    co
    cF
    @49
    @6
    @55
    @60
    @57
    cconcat
    @6
    @21
    @37
    cc0
    @19
    cfz
    co
    #
    wcel
    @55
    @60
    wceq
    @26
    @6
    @20
    @61
    @37
    cc0
    @19
    fzossfz
    @39
    sseldi
    cr
    cF
    @37
    swrd0val
    syl2anc
    #
    oveq1d
    @6
    @24
    cF
    @58
    wceq
    @25
    @24
    @58
    cF
    cr
    cF
    swrdccatwrd
    eqcomd
    syl
    @6
    @46
    @60
    @48
    @57
    cconcat
    @6
    @45
    @59
    cF
    @45
    @59
    wceq
    @6
    @3
    @37
    cc0
    cfzo
    @38
    oveq2i
    a1i
    reseq2d
    #
    @6
    @4
    @56
    @6
    @4
    @37
    cF
    cfv
    #
    @56
    @6
    @3
    @37
    cF
    @3
    @37
    wceq
    @6
    @38
    a1i
    fveq2d
    @2
    @56
    @64
    wceq
    @5
    cF
    @1
    lsw
    adantr
    eqtr4d
    s1eqd
    oveq12d
    3eqtr4d
    fveq2d
    @6
    @47
    @3
    @6
    @47
    @45
    chash
    cfv
    #
    @3
    @6
    @46
    @45
    wfn
    #
    @47
    @65
    wceq
    @6
    cF
    cc0
    cN
    cfzo
    co
    #
    wfn
    #
    @45
    @67
    wss
    #
    @66
    @6
    @68
    cF
    @20
    wfn
    #
    @6
    @21
    @22
    @70
    @26
    @28
    @20
    cr
    cF
    ffn
    3syl
    @6
    @67
    @20
    cF
    @6
    cN
    @19
    cc0
    cfzo
    cN
    @19
    wceq
    @6
    signsvtn0.1
    a1i
    oveq2d
    fneq2d
    mpbird
    @6
    cN
    cn0
    wcel
    cN
    cz
    wcel
    @69
    @6
    cN
    @6
    cN
    @19
    cn
    signsvtn0.1
    @31
    syl5eqel
    #
    nnnn0d
    cN
    nn0z
    cN
    fzossrbm1
    3syl
    @67
    @45
    cF
    fnssres
    syl2anc
    @45
    @46
    hashfn
    syl
    @6
    cN
    cn
    wcel
    #
    @3
    cn0
    wcel
    @65
    @3
    wceq
    @71
    cN
    nnm1nn0
    @3
    hashfzo0
    3syl
    eqtrd
    #
    eqcomd
    fveq12d
    adantr
    @44
    @46
    @1
    wcel
    #
    @4
    cr
    wcel
    #
    @51
    @54
    wceq
    @44
    @46
    @0
    wcel
    #
    @46
    c0
    wne
    #
    wa
    #
    @74
    @44
    @76
    @77
    @6
    @76
    @43
    @6
    @55
    @46
    @0
    @6
    @55
    @60
    @46
    @62
    @63
    eqtr4d
    @6
    @21
    @55
    @0
    wcel
    @26
    cr
    cF
    cc0
    @37
    swrdcl
    syl
    eqeltrrd
    adantr
    #
    @44
    @47
    cc0
    wne
    @77
    @44
    @47
    @3
    cc0
    @6
    @47
    @3
    wceq
    @43
    @73
    adantr
    @44
    cN
    c1
    @44
    cN
    @6
    @72
    @43
    @71
    adantr
    nncnd
    @44
    1cnd
    @6
    @43
    simpr
    subne0d
    eqnetrd
    @46
    c0
    @47
    cc0
    @46
    c0
    wceq
    @47
    c0
    chash
    cfv
    cc0
    @46
    c0
    chash
    fveq2
    hash0
    syl6eq
    necon3i
    syl
    jca
    #
    @46
    @0
    c0
    eldifsn
    sylibr
    @6
    @75
    @43
    @40
    adantr
    c.pd
    cT
    vf
    vi
    vj
    vn
    @46
    @4
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signstfvn
    syl2anc
    @44
    @53
    @34
    wcel
    #
    @35
    @9
    cc0
    wne
    #
    @54
    @9
    wceq
    @44
    @76
    @52
    cc0
    @47
    cfzo
    co
    wcel
    #
    @81
    @79
    @44
    @78
    @47
    cn
    wcel
    @83
    @80
    cr
    @46
    lennncl
    @47
    fzo0end
    3syl
    c.pd
    cT
    vf
    vi
    vj
    vn
    @46
    @52
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signstcl
    syl2anc
    @6
    @35
    @43
    @42
    adantr
    @6
    @82
    @43
    @6
    @36
    @5
    @82
    @41
    @2
    @5
    simpr
    @36
    @82
    @5
    @36
    @9
    cc0
    @4
    cc0
    @4
    sgn0bi
    necon3bid
    biimpar
    syl2anc
    adantr
    c.pd
    cW
    @53
    @9
    va
    vb
    signsv.p
    signsv.w
    signswlid
    syl21anc
    3eqtrd
    pm2.61dane
end
