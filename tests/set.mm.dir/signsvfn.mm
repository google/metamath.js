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
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "c1.mm"
include "chash.mm"
include "cfzo.mm"
include "cv.mm"
include "cmin.mm"
include "cif.mm"
include "csu.mm"
include "caddc.mm"
include "cmul.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "simpl.mm"
include "eldifad.mm"
include "simpr.mm"
include "s1cld.mm"
include "ccatcl.mm"
include "syl2anc.mm"
include "signsvvfval.mm"
include "syl.mm"
include "ccatlen.mm"
include "s1len.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "cuz.mm"
include "cn.mm"
include "eldifsn.mm"
include "lennncl.mm"
include "sylbi.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "adantr.mm"
include "cfz.mm"
include "cc.mm"
include "1cnd.mm"
include "wn.mm"
include "0cnd.mm"
include "ifclda.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "neeq12d.mm"
include "ifbid.mm"
include "fzosump1.mm"
include "3eqtrd.mm"
include "adantlr.mm"
include "wss.mm"
include "fzo0ss1.mm"
include "a1i.mm"
include "sselda.mm"
include "signstfvp.mm"
include "syl3anc.mm"
include "cz.mm"
include "cn0.mm"
include "elfzoel2.mm"
include "adantl.mm"
include "1nn0.mm"
include "eluzmn.mm"
include "sylancl.mm"
include "fzoss2.mm"
include "wb.mm"
include "elfzoelz.mm"
include "elfzom1b.mm"
include "mpbid.mm"
include "sseldd.mm"
include "sumeq2dv.mm"
include "eqtr4d.mm"
include "csgn.mm"
include "signstfvn.mm"
include "ad2antrr.mm"
include "fzo0end.mm"
include "cneg.mm"
include "cpr.mm"
include "ctp.mm"
include "signstfvcl.mm"
include "syldan.mm"
include "cxr.mm"
include "rexrd.mm"
include "sgncl.mm"
include "signswch.mm"
include "sgnsgn.mm"
include "breq1d.mm"
include "neg1rr.mm"
include "1re.mm"
include "prssi.mm"
include "mp2an.mm"
include "sseldi.mm"
include "sgnclre.mm"
include "sgnmulsgn.mm"
include "3bitr4d.mm"
include "3bitrd.mm"
include "oveq12d.mm"
include "eqtrd.mm"

theorem signsvfn
  let c.pd: class .+^
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  assume signsv.p: |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 } |-> if ( b = 0 , a , b ) )
  assume signsv.w: |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. , <. ( +g ` ndx ) , .+^ >. }
  assume signsv.t: |- T = ( f e. Word RR |-> ( n e. ( 0 ..^ ( # ` f ) ) |-> ( W gsum ( i e. ( 0 ... n ) |-> ( sgn ` ( f ` i ) ) ) ) ) )
  assume signsv.v: |- V = ( f e. Word RR |-> sum_ j e. ( 1 ..^ ( # ` f ) ) if ( ( ( T ` f ) ` j ) =/= ( ( T ` f ) ` ( j - 1 ) ) , 1 , 0 ) )

  disjoint a b
  disjoint a i
  disjoint a j
  disjoint a n
  disjoint F a
  disjoint b i
  disjoint b j
  disjoint b n
  disjoint F b
  disjoint i j
  disjoint i n
  disjoint F i
  disjoint j n
  disjoint F j
  disjoint F n
  disjoint K a
  disjoint K b
  disjoint K j
  disjoint K n
  disjoint a f
  disjoint T a
  disjoint b f
  disjoint T b
  disjoint f j
  disjoint f n
  disjoint T f
  disjoint T j
  disjoint T n
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
  assert |- ( ( ( F e. ( Word RR \ { (/) } ) /\ ( F ` 0 ) =/= 0 ) /\ K e. RR ) -> ( V ` ( F ++ <" K "> ) ) = ( ( V ` F ) + if ( ( ( ( T ` F ) ` ( ( # ` F ) - 1 ) ) x. K ) < 0 , 1 , 0 ) ) )

  proof
    cF
    cr
    cword
    #
    c0
    csn
    #
    cdif
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
    cK
    cr
    wcel
    #
    wa
    #
    cF
    cK
    cs1
    #
    cconcat
    co
    #
    cV
    cfv
    #
    c1
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    vj
    cv
    #
    @8
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
    @13
    cfv
    #
    wne
    #
    c1
    cc0
    cif
    #
    vj
    csu
    #
    @10
    @13
    cfv
    #
    @10
    c1
    cmin
    co
    #
    @13
    cfv
    #
    wne
    #
    c1
    cc0
    cif
    #
    caddc
    co
    #
    cF
    cV
    cfv
    #
    @21
    cF
    cT
    cfv
    #
    cfv
    #
    cK
    cmul
    co
    cc0
    clt
    wbr
    #
    c1
    cc0
    cif
    #
    caddc
    co
    @2
    @5
    @9
    @25
    wceq
    @3
    @2
    @5
    wa
    #
    @9
    c1
    @8
    chash
    cfv
    #
    cfzo
    co
    #
    @18
    vj
    csu
    #
    c1
    @10
    c1
    caddc
    co
    #
    cfzo
    co
    #
    @18
    vj
    csu
    @25
    @31
    @8
    @0
    wcel
    #
    @9
    @34
    wceq
    @31
    cF
    @0
    wcel
    #
    @7
    @0
    wcel
    #
    @37
    @31
    cF
    @0
    @1
    @2
    @5
    simpl
    eldifad
    #
    @31
    cK
    cr
    @2
    @5
    simpr
    #
    s1cld
    #
    cr
    cF
    @7
    ccatcl
    syl2anc
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
    signsvvfval
    syl
    @31
    @33
    @36
    @18
    vj
    @31
    @32
    @35
    c1
    cfzo
    @31
    @32
    @10
    @7
    chash
    cfv
    #
    caddc
    co
    #
    @35
    @31
    @38
    @39
    @32
    @44
    wceq
    @40
    @42
    cr
    cF
    @7
    ccatlen
    syl2anc
    @43
    c1
    @10
    caddc
    cK
    s1len
    oveq2i
    syl6eq
    oveq2d
    sumeq1d
    @31
    @18
    @24
    vj
    c1
    @10
    @2
    @10
    c1
    cuz
    cfv
    #
    wcel
    @5
    @2
    @10
    cn
    @45
    @2
    @38
    cF
    c0
    wne
    wa
    @10
    cn
    wcel
    #
    cF
    @0
    c0
    eldifsn
    cr
    cF
    lennncl
    sylbi
    #
    nnuz
    syl6eleq
    adantr
    @31
    @12
    c1
    @10
    cfz
    co
    wcel
    wa
    #
    @17
    c1
    cc0
    cc
    @48
    @17
    wa
    1cnd
    @48
    @17
    wn
    wa
    0cnd
    ifclda
    @12
    @10
    wceq
    #
    @17
    @23
    c1
    cc0
    @49
    @14
    @20
    @16
    @22
    @12
    @10
    @13
    fveq2
    @49
    @15
    @21
    @13
    @12
    @10
    c1
    cmin
    oveq1
    fveq2d
    neeq12d
    ifbid
    fzosump1
    3eqtrd
    adantlr
    @6
    @19
    @26
    @24
    @30
    caddc
    @2
    @5
    @19
    @26
    wceq
    @3
    @31
    @19
    @11
    @12
    @27
    cfv
    #
    @15
    @27
    cfv
    #
    wne
    #
    c1
    cc0
    cif
    #
    vj
    csu
    #
    @26
    @31
    @11
    @18
    @53
    vj
    @31
    @12
    @11
    wcel
    #
    wa
    #
    @17
    @52
    c1
    cc0
    @56
    @14
    @50
    @16
    @51
    @56
    @38
    @5
    @12
    cc0
    @10
    cfzo
    co
    #
    wcel
    @14
    @50
    wceq
    @31
    @38
    @55
    @40
    adantr
    #
    @31
    @5
    @55
    @41
    adantr
    #
    @31
    @11
    @57
    @12
    @11
    @57
    wss
    @31
    @10
    fzo0ss1
    a1i
    sselda
    c.pd
    cT
    vf
    vi
    vj
    vn
    cF
    cK
    @12
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
    @56
    @38
    @5
    @15
    @57
    wcel
    @16
    @51
    wceq
    @58
    @59
    @56
    cc0
    @21
    cfzo
    co
    #
    @57
    @15
    @56
    @10
    @21
    cuz
    cfv
    wcel
    #
    @60
    @57
    wss
    @56
    @10
    cz
    wcel
    #
    c1
    cn0
    wcel
    @61
    @55
    @62
    @31
    @12
    c1
    @10
    elfzoel2
    adantl
    #
    1nn0
    @10
    c1
    eluzmn
    sylancl
    @21
    cc0
    @10
    fzoss2
    syl
    @56
    @55
    @15
    @60
    wcel
    #
    @31
    @55
    simpr
    @56
    @12
    cz
    wcel
    #
    @62
    @55
    @64
    wb
    @55
    @65
    @31
    @12
    c1
    @10
    elfzoelz
    adantl
    @63
    @12
    @10
    elfzom1b
    syl2anc
    mpbid
    sseldd
    c.pd
    cT
    vf
    vi
    vj
    vn
    cF
    cK
    @15
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
    neeq12d
    ifbid
    sumeq2dv
    @31
    @38
    @26
    @54
    wceq
    @40
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
    signsvvfval
    syl
    eqtr4d
    adantlr
    @6
    @23
    @29
    c1
    cc0
    @6
    @23
    @28
    cK
    csgn
    cfv
    #
    c.pd
    co
    #
    @28
    wne
    #
    @28
    @66
    cmul
    co
    cc0
    clt
    wbr
    #
    @29
    @6
    @20
    @67
    @22
    @28
    @2
    @5
    @20
    @67
    wceq
    @3
    c.pd
    cT
    vf
    vi
    vj
    vn
    cF
    cK
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signstfvn
    adantlr
    @6
    @38
    @5
    @21
    @57
    wcel
    #
    @22
    @28
    wceq
    @2
    @5
    @38
    @3
    @40
    adantlr
    @4
    @5
    simpr
    #
    @6
    @46
    @70
    @2
    @46
    @3
    @5
    @47
    ad2antrr
    @10
    fzo0end
    syl
    #
    c.pd
    cT
    vf
    vi
    vj
    vn
    cF
    cK
    @21
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
    neeq12d
    @6
    @28
    c1
    cneg
    #
    c1
    cpr
    #
    wcel
    #
    @66
    @73
    cc0
    c1
    ctp
    wcel
    #
    @68
    @69
    wb
    @4
    @5
    @70
    @75
    @72
    c.pd
    cT
    vf
    vi
    vj
    vn
    cF
    @21
    cV
    cW
    va
    vb
    signsv.p
    signsv.w
    signsv.t
    signsv.v
    signstfvcl
    syldan
    #
    @6
    cK
    cxr
    wcel
    #
    @76
    @6
    cK
    @71
    rexrd
    #
    cK
    sgncl
    syl
    c.pd
    cW
    @28
    @66
    va
    vb
    signsv.p
    signsv.w
    signswch
    syl2anc
    @6
    @28
    csgn
    cfv
    #
    @66
    csgn
    cfv
    #
    cmul
    co
    #
    cc0
    clt
    wbr
    #
    @80
    @66
    cmul
    co
    #
    cc0
    clt
    wbr
    #
    @69
    @29
    @6
    @82
    @84
    cc0
    clt
    @6
    @81
    @66
    @80
    cmul
    @6
    @78
    @81
    @66
    wceq
    @79
    cK
    sgnsgn
    syl
    oveq2d
    breq1d
    @6
    @28
    cr
    wcel
    #
    @66
    cr
    wcel
    #
    @69
    @83
    wb
    @6
    @74
    cr
    @28
    @73
    cr
    wcel
    c1
    cr
    wcel
    @74
    cr
    wss
    neg1rr
    1re
    @73
    c1
    cr
    prssi
    mp2an
    @77
    sseldi
    #
    @5
    @87
    @4
    cK
    sgnclre
    adantl
    @28
    @66
    sgnmulsgn
    syl2anc
    @6
    @86
    @5
    @29
    @85
    wb
    @88
    @71
    @28
    cK
    sgnmulsgn
    syl2anc
    3bitr4d
    3bitrd
    ifbid
    oveq12d
    eqtrd
end
