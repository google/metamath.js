include "cr.mm"
include "cword.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cs1.mm"
include "cconcat.mm"
include "csgn.mm"
include "cmpt.mm"
include "cgsu.mm"
include "c1.mm"
include "cmin.mm"
include "caddc.mm"
include "cneg.mm"
include "ctp.mm"
include "signswbase.mm"
include "cmnd.mm"
include "signswmnd.mm"
include "a1i.mm"
include "cn0.mm"
include "cuz.mm"
include "cn.mm"
include "wne.mm"
include "eldifi.mm"
include "lencl.mm"
include "syl.mm"
include "eldifsn.mm"
include "hasheq0.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "sylbi.mm"
include "elnnne0.mm"
include "sylanbrc.mm"
include "adantr.mm"
include "nnm1nn0.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "cxr.mm"
include "cfzo.mm"
include "wf.mm"
include "s1cl.mm"
include "ccatcl.mm"
include "syl2an.mm"
include "wrdf.mm"
include "cz.mm"
include "wceq.mm"
include "nn0zd.mm"
include "fzoval.mm"
include "fzossfz.mm"
include "syl6eqssr.mm"
include "ccatlen.mm"
include "s1len.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "peano2zd.mm"
include "nn0cnd.mm"
include "1cnd.mm"
include "pncand.mm"
include "3eqtrd.mm"
include "sseqtr4d.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "rexrd.mm"
include "sgncl.mm"
include "signswplusg.mm"
include "simpr.mm"
include "npcand.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "c0ex.mm"
include "snid.mm"
include "fzo01.mm"
include "eleqtrri.mm"
include "ccatval3.mm"
include "syl3anc.mm"
include "addid2d.mm"
include "s1fv.mm"
include "3eqtr3d.mm"
include "gsumnunsn.mm"
include "mpteq1d.mm"
include "eleq2d.mm"
include "ccatval1.mm"
include "mpteq2dva.mm"
include "oveq1d.mm"
include "wo.mm"
include "eqidd.mm"
include "olcd.mm"
include "wb.mm"
include "fzosplitsni.mm"
include "mpbird.mm"
include "eleqtrrd.mm"
include "signstfval.mm"
include "syl2anc.mm"
include "fzo0end.mm"
include "3eqtr4d.mm"

theorem signstfvn
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
  assert |- ( ( F e. ( Word RR \ { (/) } ) /\ K e. RR ) -> ( ( T ` ( F ++ <" K "> ) ) ` ( # ` F ) ) = ( ( ( T ` F ) ` ( ( # ` F ) - 1 ) ) .+^ ( sgn ` K ) ) )

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
    cK
    cr
    wcel
    #
    wa
    #
    cW
    vi
    cc0
    cF
    chash
    cfv
    #
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
    cc0
    @5
    c1
    cmin
    co
    #
    cfz
    co
    #
    @7
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
    cK
    csgn
    cfv
    #
    c.pd
    co
    #
    @5
    @9
    cT
    cfv
    cfv
    #
    @14
    cF
    cT
    cfv
    cfv
    #
    @20
    c.pd
    co
    @4
    cW
    vi
    cc0
    @14
    c1
    caddc
    co
    #
    cfz
    co
    #
    @11
    cmpt
    #
    cgsu
    co
    cW
    vi
    @15
    @11
    cmpt
    #
    cgsu
    co
    #
    @20
    c.pd
    co
    @13
    @21
    @4
    @11
    @20
    @14
    c.pd
    vi
    c1
    cneg
    cc0
    c1
    ctp
    #
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
    @4
    @14
    cn0
    cc0
    cuz
    cfv
    #
    @4
    @5
    cn
    wcel
    #
    @14
    cn0
    wcel
    @2
    @31
    @3
    @2
    @5
    cn0
    wcel
    #
    @5
    cc0
    wne
    #
    @31
    @2
    cF
    @0
    wcel
    #
    @32
    cF
    @0
    @1
    eldifi
    #
    cr
    cF
    lencl
    syl
    #
    @2
    @34
    cF
    c0
    wne
    #
    wa
    @33
    cF
    @0
    c0
    eldifsn
    @34
    @33
    @37
    @34
    @5
    cc0
    cF
    c0
    cF
    @0
    hasheq0
    necon3bid
    biimpar
    sylbi
    @5
    elnnne0
    sylanbrc
    #
    adantr
    @5
    nnm1nn0
    syl
    nn0uz
    syl6eleq
    @4
    @7
    @15
    wcel
    #
    wa
    #
    @10
    cxr
    wcel
    @11
    @29
    wcel
    @40
    @10
    @40
    cc0
    @9
    chash
    cfv
    #
    cfzo
    co
    #
    cr
    @7
    @9
    @40
    @9
    @0
    wcel
    #
    @42
    cr
    @9
    wf
    @4
    @43
    @39
    @2
    @34
    @8
    @0
    wcel
    #
    @43
    @3
    @35
    cK
    cr
    s1cl
    #
    cr
    cF
    @8
    ccatcl
    syl2an
    #
    adantr
    cr
    @9
    wrdf
    syl
    @4
    @15
    @42
    @7
    @4
    @15
    @6
    @42
    @4
    @15
    cc0
    @5
    cfzo
    co
    #
    @6
    @4
    @5
    cz
    wcel
    @47
    @15
    wceq
    @4
    @5
    @2
    @32
    @3
    @36
    adantr
    #
    nn0zd
    #
    cc0
    @5
    fzoval
    syl
    #
    cc0
    @5
    fzossfz
    syl6eqssr
    @4
    @42
    cc0
    @5
    c1
    caddc
    co
    #
    cfzo
    co
    #
    cc0
    @51
    c1
    cmin
    co
    #
    cfz
    co
    #
    @6
    @4
    @41
    @51
    cc0
    cfzo
    @4
    @41
    @5
    @8
    chash
    cfv
    #
    caddc
    co
    #
    @51
    @2
    @34
    @44
    @41
    @56
    wceq
    @3
    @35
    @45
    cr
    cF
    @8
    ccatlen
    syl2an
    @55
    c1
    @5
    caddc
    cK
    s1len
    #
    oveq2i
    syl6eq
    oveq2d
    #
    @4
    @51
    cz
    wcel
    @52
    @54
    wceq
    @4
    @5
    @49
    peano2zd
    cc0
    @51
    fzoval
    syl
    @4
    @53
    @5
    cc0
    cfz
    @4
    @5
    c1
    @4
    @5
    @48
    nn0cnd
    #
    @4
    1cnd
    #
    pncand
    oveq2d
    3eqtrd
    sseqtr4d
    sselda
    ffvelrnd
    rexrd
    @10
    sgncl
    syl
    c.pd
    cW
    va
    vb
    signsv.p
    signsv.w
    signswplusg
    @4
    cK
    cxr
    wcel
    @20
    @29
    wcel
    @4
    cK
    @2
    @3
    simpr
    #
    rexrd
    cK
    sgncl
    syl
    @4
    @7
    @24
    wceq
    #
    wa
    #
    @10
    cK
    csgn
    @63
    @10
    @5
    @9
    cfv
    #
    cK
    @63
    @7
    @5
    @9
    @63
    @7
    @24
    @5
    @4
    @62
    simpr
    @4
    @24
    @5
    wceq
    @62
    @4
    @5
    c1
    @59
    @60
    npcand
    #
    adantr
    eqtrd
    fveq2d
    @4
    @64
    cK
    wceq
    @62
    @4
    cc0
    @5
    caddc
    co
    #
    @9
    cfv
    #
    cc0
    @8
    cfv
    #
    @64
    cK
    @4
    @34
    @44
    cc0
    cc0
    @55
    cfzo
    co
    #
    wcel
    #
    @67
    @68
    wceq
    @2
    @34
    @3
    @35
    adantr
    #
    @4
    @3
    @44
    @61
    @45
    syl
    #
    @70
    @4
    cc0
    cc0
    c1
    cfzo
    co
    #
    @69
    cc0
    cc0
    csn
    @73
    cc0
    c0ex
    snid
    fzo01
    eleqtrri
    @55
    c1
    cc0
    cfzo
    @57
    oveq2i
    eleqtrri
    a1i
    cr
    cF
    @8
    cc0
    ccatval3
    syl3anc
    @4
    @66
    @5
    @9
    @4
    @5
    @59
    addid2d
    fveq2d
    @4
    @3
    @68
    cK
    wceq
    @61
    cK
    cr
    s1fv
    syl
    3eqtr3d
    adantr
    eqtrd
    fveq2d
    gsumnunsn
    @4
    @26
    @12
    cW
    cgsu
    @4
    vi
    @25
    @6
    @11
    @4
    @24
    @5
    cc0
    cfz
    @65
    oveq2d
    mpteq1d
    oveq2d
    @4
    @28
    @19
    @20
    c.pd
    @4
    @27
    @18
    cW
    cgsu
    @4
    vi
    @15
    @11
    @17
    @40
    @10
    @16
    csgn
    @40
    @34
    @44
    @7
    @47
    wcel
    #
    @10
    @16
    wceq
    @4
    @34
    @39
    @71
    adantr
    @4
    @44
    @39
    @72
    adantr
    @4
    @74
    @39
    @4
    @47
    @15
    @7
    @50
    eleq2d
    biimpar
    cr
    cF
    @8
    @7
    ccatval1
    syl3anc
    fveq2d
    mpteq2dva
    oveq2d
    oveq1d
    3eqtr3d
    @4
    @43
    @5
    @42
    wcel
    @22
    @13
    wceq
    @46
    @4
    @5
    @52
    @42
    @4
    @5
    @52
    wcel
    #
    @5
    @47
    wcel
    #
    @5
    @5
    wceq
    #
    wo
    #
    @4
    @77
    @76
    @4
    @5
    eqidd
    olcd
    @4
    @5
    @30
    wcel
    @75
    @78
    wb
    @4
    @5
    cn0
    @30
    @48
    nn0uz
    syl6eleq
    cc0
    @5
    @5
    fzosplitsni
    syl
    mpbird
    @58
    eleqtrrd
    c.pd
    cT
    vf
    vi
    vj
    vn
    @9
    @5
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
    @4
    @23
    @19
    @20
    c.pd
    @2
    @23
    @19
    wceq
    #
    @3
    @2
    @34
    @14
    @47
    wcel
    #
    @79
    @35
    @2
    @31
    @80
    @38
    @5
    fzo0end
    syl
    c.pd
    cT
    vf
    vi
    vj
    vn
    cF
    @14
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
    adantr
    oveq1d
    3eqtr4d
end
