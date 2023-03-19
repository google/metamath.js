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
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "cop.mm"
include "csubstr.mm"
include "chash.mm"
include "cs1.mm"
include "cconcat.mm"
include "csgn.mm"
include "c2.mm"
include "simpll.mm"
include "eldifad.mm"
include "swrdcl.mm"
include "syl.mm"
include "cn.mm"
include "cfz.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "1nn0.mm"
include "a1i.mm"
include "nn0red.mm"
include "2re.mm"
include "lencl.mm"
include "syl5eqel.mm"
include "1le2.mm"
include "cz.mm"
include "cuz.mm"
include "w3a.mm"
include "signstfveq0a.mm"
include "eluz2.mm"
include "sylib.mm"
include "simp3d.mm"
include "letrd.mm"
include "wb.mm"
include "fznn0.mm"
include "mpbir2and.mm"
include "fznn0sub2.mm"
include "oveq2i.mm"
include "syl6eleq.mm"
include "swrd0len.mm"
include "syl2anc.mm"
include "uz2m1nn.mm"
include "eqeltrd.mm"
include "nnne0.mm"
include "fveq2.mm"
include "hash0.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "simpr.mm"
include "0re.mm"
include "syl6eqel.mm"
include "signstfvn.mm"
include "clsw.mm"
include "oveq1i.mm"
include "opeq2i.mm"
include "lsw.mm"
include "ad2antrr.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "s1eqd.mm"
include "eqcomd.mm"
include "oveq12d.mm"
include "swrdccatwrd.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "fveq12d.mm"
include "cfzo.mm"
include "caddc.mm"
include "nn0cnd.mm"
include "1cnd.mm"
include "subsub4d.mm"
include "1p1e2.mm"
include "fzo0end.mm"
include "eqeltrrd.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"
include "signstfvp.mm"
include "syl3anc.mm"
include "fveq1d.mm"
include "oveq1d.mm"
include "3eqtr4rd.mm"
include "sgn0.mm"
include "adantl.mm"
include "cneg.mm"
include "ctp.mm"
include "clt.mm"
include "uznn0sub.mm"
include "eluz2nn.mm"
include "crp.mm"
include "2rp.mm"
include "ltsubrpd.mm"
include "elfzo0.mm"
include "syl3anbrc.mm"
include "signstcl.mm"
include "signswrid.mm"
include "3eqtr3d.mm"

theorem signstfveq0
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
  assume signstfveq0.1: |- N = ( # ` F )

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
  assert |- ( ( ( F e. ( Word RR \ { (/) } ) /\ ( F ` 0 ) =/= 0 ) /\ ( F ` ( N - 1 ) ) = 0 ) -> ( ( T ` F ) ` ( N - 1 ) ) = ( ( T ` F ) ` ( N - 2 ) ) )

  proof
    cF
    cr
    cword
    #
    c0
    csn
    #
    cdif
    #
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
    c1
    cmin
    co
    #
    cF
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    cF
    cc0
    @6
    cop
    #
    csubstr
    co
    #
    chash
    cfv
    #
    @11
    @7
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
    @12
    c1
    cmin
    co
    #
    @11
    cT
    cfv
    #
    cfv
    #
    @7
    csgn
    cfv
    #
    c.pd
    co
    #
    @6
    cF
    cT
    cfv
    #
    cfv
    cN
    c2
    cmin
    co
    #
    @22
    cfv
    #
    @9
    @11
    @2
    wcel
    #
    @7
    cr
    wcel
    #
    @16
    @21
    wceq
    @9
    @11
    @0
    wcel
    #
    @11
    c0
    wne
    #
    @25
    @9
    cF
    @0
    wcel
    #
    @27
    @9
    cF
    @0
    @1
    @3
    @4
    @8
    simpll
    #
    eldifad
    #
    cr
    cF
    cc0
    @6
    swrdcl
    syl
    #
    @9
    @12
    cn
    wcel
    #
    @28
    @9
    @12
    @6
    cn
    @9
    @29
    @6
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    @12
    @6
    wceq
    @31
    @9
    @6
    cc0
    cN
    cfz
    co
    #
    @35
    @9
    c1
    @36
    wcel
    #
    @6
    @36
    wcel
    @9
    @37
    c1
    cn0
    wcel
    #
    c1
    cN
    cle
    wbr
    #
    @38
    @9
    1nn0
    a1i
    #
    @9
    c1
    c2
    cN
    @9
    c1
    @40
    nn0red
    c2
    cr
    wcel
    @9
    2re
    a1i
    @9
    cN
    @9
    cN
    @34
    cn0
    signstfveq0.1
    @9
    @29
    @34
    cn0
    wcel
    @31
    cr
    cF
    lencl
    syl
    syl5eqel
    #
    nn0red
    #
    c1
    c2
    cle
    wbr
    @9
    1le2
    a1i
    @9
    c2
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    c2
    cN
    cle
    wbr
    #
    @9
    cN
    c2
    cuz
    cfv
    wcel
    #
    @43
    @44
    @45
    w3a
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
    signstfveq0.1
    signstfveq0a
    #
    c2
    cN
    eluz2
    sylib
    simp3d
    letrd
    @9
    cN
    cn0
    wcel
    @37
    @38
    @39
    wa
    wb
    @41
    c1
    cN
    fznn0
    syl
    mpbir2and
    c1
    cN
    fznn0sub2
    syl
    cN
    @34
    cc0
    cfz
    signstfveq0.1
    oveq2i
    syl6eleq
    cr
    cF
    @6
    swrd0len
    syl2anc
    #
    @9
    @46
    @6
    cn
    wcel
    #
    @47
    cN
    uz2m1nn
    syl
    #
    eqeltrd
    @33
    @12
    cc0
    wne
    @28
    @12
    nnne0
    @11
    c0
    @12
    cc0
    @11
    c0
    wceq
    @12
    c0
    chash
    cfv
    cc0
    @11
    c0
    chash
    fveq2
    hash0
    syl6eq
    necon3i
    syl
    syl
    @11
    @0
    c0
    eldifsn
    sylanbrc
    @9
    @7
    cc0
    cr
    @5
    @8
    simpr
    0re
    syl6eqel
    #
    c.pd
    cT
    vf
    vi
    vj
    vn
    @11
    @7
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
    @9
    @12
    @6
    @15
    @22
    @9
    @14
    cF
    cT
    @9
    @14
    cF
    cc0
    @34
    c1
    cmin
    co
    #
    cop
    #
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
    @9
    @11
    @54
    @13
    @56
    cconcat
    @11
    @54
    wceq
    @9
    @10
    @53
    cF
    csubstr
    @6
    @52
    cc0
    cN
    @34
    c1
    cmin
    signstfveq0.1
    oveq1i
    opeq2i
    oveq2i
    a1i
    @9
    @56
    @13
    @9
    @55
    @7
    @9
    @55
    @52
    cF
    cfv
    #
    @7
    @3
    @55
    @58
    wceq
    @4
    @8
    cF
    @2
    lsw
    ad2antrr
    @52
    @6
    cF
    @34
    cN
    c1
    cmin
    cN
    @34
    signstfveq0.1
    eqcomi
    oveq1i
    fveq2i
    syl6eq
    s1eqd
    eqcomd
    oveq12d
    @9
    @29
    cF
    c0
    wne
    wa
    #
    @57
    cF
    wceq
    @9
    @3
    @59
    @30
    cF
    @0
    c0
    eldifsn
    sylib
    cr
    cF
    swrdccatwrd
    syl
    eqtrd
    #
    fveq2d
    @48
    fveq12d
    @9
    @21
    @24
    cc0
    c.pd
    co
    #
    @24
    @9
    @19
    @24
    @20
    cc0
    c.pd
    @9
    @23
    @15
    cfv
    #
    @23
    @18
    cfv
    #
    @24
    @19
    @9
    @27
    @26
    @23
    cc0
    @12
    cfzo
    co
    #
    wcel
    @62
    @63
    wceq
    @32
    @51
    @9
    @23
    cc0
    @6
    cfzo
    co
    #
    @64
    @9
    @6
    c1
    cmin
    co
    #
    @23
    @65
    @9
    @66
    cN
    c1
    c1
    caddc
    co
    #
    cmin
    co
    #
    @23
    @9
    cN
    c1
    c1
    @9
    cN
    @41
    nn0cnd
    @9
    1cnd
    #
    @69
    subsub4d
    #
    @67
    c2
    cN
    cmin
    1p1e2
    oveq2i
    #
    syl6eq
    @9
    @49
    @66
    @65
    wcel
    @50
    @6
    fzo0end
    syl
    eqeltrrd
    @9
    @12
    @6
    cc0
    cfzo
    @48
    oveq2d
    eleqtrrd
    c.pd
    cT
    vf
    vi
    vj
    vn
    @11
    @7
    @23
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
    @9
    @23
    @22
    @15
    @9
    cF
    @14
    cT
    @9
    @14
    cF
    @60
    eqcomd
    fveq2d
    fveq1d
    @9
    @17
    @23
    @18
    @9
    @17
    @68
    @23
    @9
    @17
    @66
    @68
    @9
    @12
    @6
    c1
    cmin
    @48
    oveq1d
    @70
    eqtrd
    @71
    syl6eq
    fveq2d
    3eqtr4rd
    @8
    @20
    cc0
    wceq
    @5
    @8
    @20
    cc0
    csgn
    cfv
    cc0
    @7
    cc0
    csgn
    fveq2
    sgn0
    syl6eq
    adantl
    oveq12d
    @9
    @24
    c1
    cneg
    cc0
    c1
    ctp
    wcel
    #
    @61
    @24
    wceq
    @9
    @29
    @23
    cc0
    @34
    cfzo
    co
    #
    wcel
    @72
    @31
    @9
    @23
    cc0
    cN
    cfzo
    co
    #
    @73
    @9
    @23
    cn0
    wcel
    #
    cN
    cn
    wcel
    #
    @23
    cN
    clt
    wbr
    @23
    @74
    wcel
    @9
    @46
    @75
    @47
    c2
    cN
    uznn0sub
    syl
    @9
    @46
    @76
    @47
    cN
    eluz2nn
    syl
    @9
    cN
    c2
    @42
    c2
    crp
    wcel
    @9
    2rp
    a1i
    ltsubrpd
    @23
    cN
    elfzo0
    syl3anbrc
    cN
    @34
    cc0
    cfzo
    signstfveq0.1
    oveq2i
    syl6eleq
    c.pd
    cT
    vf
    vi
    vj
    vn
    cF
    @23
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
    c.pd
    cW
    @24
    va
    vb
    signsv.p
    signsv.w
    signswrid
    syl
    eqtrd
    3eqtr3d
end
