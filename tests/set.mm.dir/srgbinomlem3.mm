include "wa.mm"
include "co.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "cbc.mm"
include "cmin.mm"
include "cmpt.mm"
include "cgsu.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "adantl.mm"
include "oveq1d.mm"
include "csn.mm"
include "c0g.mm"
include "cfv.mm"
include "csrg.mm"
include "wcel.mm"
include "ccmn.mm"
include "srgcmn.mm"
include "syl.mm"
include "cn0.mm"
include "simpl.mm"
include "cz.mm"
include "elfzelz.mm"
include "bccl.mm"
include "syl2an.mm"
include "fznn0sub.mm"
include "elfznn0.mm"
include "srgbinomlem2.mm"
include "syl13anc.mm"
include "gsummptfzsplit.mm"
include "cmnd.mm"
include "cvv.mm"
include "srgmnd.mm"
include "ovexd.mm"
include "id.mm"
include "nn0zd.mm"
include "peano2zd.mm"
include "syl2anc.mm"
include "cc.mm"
include "nn0cnd.mm"
include "peano2cn.mm"
include "subidd.mm"
include "0nn0.mm"
include "syl6eqel.mm"
include "peano2nn0.mm"
include "oveq2.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "gsumsn.mm"
include "syl3anc.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "nn0red.mm"
include "ltp1d.mm"
include "olcd.mm"
include "bcval4.mm"
include "srgbinomlem1.mm"
include "syl12anc.mm"
include "eqid.mm"
include "mulg0.mm"
include "3eqtrd.mm"
include "oveq2d.mm"
include "fzfid.mm"
include "bccl2.mm"
include "nnnn0d.mm"
include "fzelp1.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "gsummptcl.mm"
include "mndrid.mm"
include "adantr.mm"
include "srgpcomppsc.mm"
include "1cnd.mm"
include "zcnd.mm"
include "addsubd.mm"
include "eqtr4d.mm"
include "mpteq2dva.mm"
include "fvexd.mm"
include "fsuppmptdm.mm"
include "srgsummulcr.mm"
include "3eqtr2rd.mm"
include "eqtrd.mm"

theorem srgbinomlem3
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let vk: setvar k
  let c.ex: class .^
  let cG: class G
  let cN: class N
  assume srgbinom.s: |- S = ( Base ` R )
  assume srgbinom.m: |- .X. = ( .r ` R )
  assume srgbinom.t: |- .x. = ( .g ` R )
  assume srgbinom.a: |- .+ = ( +g ` R )
  assume srgbinom.g: |- G = ( mulGrp ` R )
  assume srgbinom.e: |- .^ = ( .g ` G )
  assume srgbinomlem.r: |- ( ph -> R e. SRing )
  assume srgbinomlem.a: |- ( ph -> A e. S )
  assume srgbinomlem.b: |- ( ph -> B e. S )
  assume srgbinomlem.c: |- ( ph -> ( A .X. B ) = ( B .X. A ) )
  assume srgbinomlem.n: |- ( ph -> N e. NN0 )
  assume srgbinomlem.i: |- ( ps -> ( N .^ ( A .+ B ) ) = ( R gsum ( k e. ( 0 ... N ) |-> ( ( N _C k ) .x. ( ( ( N - k ) .^ A ) .X. ( k .^ B ) ) ) ) ) )

  disjoint A k
  disjoint B k
  disjoint N k
  disjoint R k
  disjoint S k
  disjoint .x. k
  disjoint .X. k
  disjoint .^ k
  disjoint k ph
  assert |- ( ( ph /\ ps ) -> ( ( N .^ ( A .+ B ) ) .X. A ) = ( R gsum ( k e. ( 0 ... ( N + 1 ) ) |-> ( ( N _C k ) .x. ( ( ( ( N + 1 ) - k ) .^ A ) .X. ( k .^ B ) ) ) ) ) )

  proof
    wph
    wps
    wa
    #
    cN
    cA
    cB
    c.pl
    co
    c.ex
    co
    #
    cA
    c.xp
    co
    cR
    vk
    cc0
    cN
    cfz
    co
    #
    cN
    vk
    cv
    #
    cbc
    co
    #
    cN
    @3
    cmin
    co
    #
    cA
    c.ex
    co
    @3
    cB
    c.ex
    co
    #
    c.xp
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cA
    c.xp
    co
    #
    cR
    vk
    cc0
    cN
    c1
    caddc
    co
    #
    cfz
    co
    #
    @4
    @12
    @3
    cmin
    co
    #
    cA
    c.ex
    co
    #
    @6
    c.xp
    co
    #
    c.x
    co
    #
    cmpt
    cgsu
    co
    #
    @0
    @1
    @10
    cA
    c.xp
    wps
    @1
    @10
    wceq
    wph
    srgbinomlem.i
    adantl
    oveq1d
    wph
    @11
    @18
    wceq
    wps
    wph
    @18
    cR
    vk
    @2
    @17
    cmpt
    #
    cgsu
    co
    #
    cR
    vk
    @2
    @8
    cA
    c.xp
    co
    #
    cmpt
    #
    cgsu
    co
    @11
    wph
    @18
    @20
    cR
    vk
    @12
    csn
    @17
    cmpt
    cgsu
    co
    #
    c.pl
    co
    @20
    cR
    c0g
    cfv
    #
    c.pl
    co
    #
    @20
    wph
    cS
    c.pl
    vk
    cR
    cN
    @17
    srgbinom.s
    srgbinom.a
    wph
    cR
    csrg
    wcel
    #
    cR
    ccmn
    wcel
    srgbinomlem.r
    cR
    srgcmn
    syl
    #
    srgbinomlem.n
    wph
    @3
    @13
    wcel
    #
    wa
    wph
    @4
    cn0
    wcel
    #
    @14
    cn0
    wcel
    #
    @3
    cn0
    wcel
    #
    @17
    cS
    wcel
    #
    wph
    @28
    simpl
    wph
    cN
    cn0
    wcel
    #
    @3
    cz
    wcel
    @29
    @28
    srgbinomlem.n
    @3
    cc0
    @12
    elfzelz
    @3
    cN
    bccl
    syl2an
    @28
    @30
    wph
    @3
    cc0
    @12
    fznn0sub
    adantl
    #
    @28
    @31
    wph
    @3
    @12
    elfznn0
    adantl
    wph
    cA
    cB
    @4
    @14
    c.pl
    cR
    cS
    c.x
    c.xp
    @3
    c.ex
    cG
    cN
    srgbinom.s
    srgbinom.m
    srgbinom.t
    srgbinom.a
    srgbinom.g
    srgbinom.e
    srgbinomlem.r
    srgbinomlem.a
    srgbinomlem.b
    srgbinomlem.c
    srgbinomlem.n
    srgbinomlem2
    #
    syl13anc
    gsummptfzsplit
    wph
    @23
    @24
    @20
    c.pl
    wph
    @23
    cN
    @12
    cbc
    co
    #
    @12
    @12
    cmin
    co
    #
    cA
    c.ex
    co
    #
    @12
    cB
    c.ex
    co
    #
    c.xp
    co
    #
    c.x
    co
    #
    cc0
    @40
    c.x
    co
    #
    @24
    wph
    cR
    cmnd
    wcel
    #
    @12
    cvv
    wcel
    @41
    cS
    wcel
    #
    @23
    @41
    wceq
    wph
    @26
    @43
    srgbinomlem.r
    cR
    srgmnd
    syl
    #
    wph
    cN
    c1
    caddc
    ovexd
    wph
    wph
    @36
    cn0
    wcel
    #
    @37
    cn0
    wcel
    #
    @12
    cn0
    wcel
    #
    @44
    wph
    id
    #
    wph
    @33
    @12
    cz
    wcel
    #
    @46
    srgbinomlem.n
    wph
    cN
    wph
    cN
    srgbinomlem.n
    nn0zd
    peano2zd
    #
    @12
    cN
    bccl
    syl2anc
    wph
    @37
    cc0
    cn0
    wph
    @12
    wph
    cN
    cc
    wcel
    #
    @12
    cc
    wcel
    wph
    cN
    srgbinomlem.n
    nn0cnd
    #
    cN
    peano2cn
    syl
    subidd
    0nn0
    syl6eqel
    #
    wph
    @33
    @48
    srgbinomlem.n
    cN
    peano2nn0
    syl
    #
    wph
    cA
    cB
    @36
    @37
    c.pl
    cR
    cS
    c.x
    c.xp
    @12
    c.ex
    cG
    cN
    srgbinom.s
    srgbinom.m
    srgbinom.t
    srgbinom.a
    srgbinom.g
    srgbinom.e
    srgbinomlem.r
    srgbinomlem.a
    srgbinomlem.b
    srgbinomlem.c
    srgbinomlem.n
    srgbinomlem2
    syl13anc
    @17
    cS
    @41
    vk
    cR
    @12
    cvv
    srgbinom.s
    @3
    @12
    wceq
    #
    @4
    @36
    @16
    @40
    c.x
    @3
    @12
    cN
    cbc
    oveq2
    @56
    @15
    @38
    @6
    @39
    c.xp
    @56
    @14
    @37
    cA
    c.ex
    @3
    @12
    @12
    cmin
    oveq2
    oveq1d
    @3
    @12
    cB
    c.ex
    oveq1
    oveq12d
    oveq12d
    gsumsn
    syl3anc
    wph
    @36
    cc0
    @40
    c.x
    wph
    @33
    @50
    @12
    cc0
    clt
    wbr
    #
    cN
    @12
    clt
    wbr
    #
    wo
    @36
    cc0
    wceq
    srgbinomlem.n
    @51
    wph
    @58
    @57
    wph
    cN
    wph
    cN
    srgbinomlem.n
    nn0red
    ltp1d
    olcd
    @12
    cN
    bcval4
    syl3anc
    oveq1d
    wph
    @40
    cS
    wcel
    #
    @42
    @24
    wceq
    wph
    wph
    @47
    @48
    @59
    @49
    @54
    @55
    wph
    cA
    cB
    @37
    c.pl
    cR
    cS
    c.x
    c.xp
    @12
    c.ex
    cG
    cN
    srgbinom.s
    srgbinom.m
    srgbinom.t
    srgbinom.a
    srgbinom.g
    srgbinom.e
    srgbinomlem.r
    srgbinomlem.a
    srgbinomlem.b
    srgbinomlem.c
    srgbinomlem.n
    srgbinomlem1
    syl12anc
    cS
    c.x
    cR
    @40
    @24
    srgbinom.s
    @24
    eqid
    #
    srgbinom.t
    mulg0
    syl
    3eqtrd
    oveq2d
    wph
    @43
    @20
    cS
    wcel
    @25
    @20
    wceq
    @45
    wph
    cS
    vk
    cR
    @2
    @17
    srgbinom.s
    @27
    wph
    cc0
    cN
    fzfid
    #
    wph
    @32
    vk
    @2
    wph
    @3
    @2
    wcel
    #
    wa
    #
    wph
    @29
    @30
    @31
    @32
    wph
    @62
    simpl
    #
    @62
    @29
    wph
    @62
    @4
    @3
    cN
    bccl2
    nnnn0d
    adantl
    #
    @62
    wph
    @28
    @30
    @3
    cc0
    cN
    fzelp1
    @34
    sylan2
    @62
    @31
    wph
    @3
    cN
    elfznn0
    adantl
    #
    @35
    syl13anc
    ralrimiva
    gsummptcl
    cS
    c.pl
    cR
    @20
    @24
    srgbinom.s
    srgbinom.a
    @60
    mndrid
    syl2anc
    3eqtrd
    wph
    @22
    @19
    cR
    cgsu
    wph
    vk
    @2
    @21
    @17
    @63
    @21
    @4
    @5
    c1
    caddc
    co
    #
    cA
    c.ex
    co
    #
    @6
    c.xp
    co
    #
    c.x
    co
    @17
    @63
    cA
    cB
    @4
    cR
    cS
    c.x
    c.xp
    c.ex
    cG
    @3
    @5
    srgbinom.s
    srgbinom.m
    srgbinom.g
    srgbinom.e
    wph
    @26
    @62
    srgbinomlem.r
    adantr
    wph
    cA
    cS
    wcel
    @62
    srgbinomlem.a
    adantr
    wph
    cB
    cS
    wcel
    @62
    srgbinomlem.b
    adantr
    @66
    wph
    cA
    cB
    c.xp
    co
    cB
    cA
    c.xp
    co
    wceq
    @62
    srgbinomlem.c
    adantr
    @62
    @5
    cn0
    wcel
    #
    wph
    @3
    cc0
    cN
    fznn0sub
    adantl
    #
    srgbinom.t
    @65
    srgpcomppsc
    @63
    @16
    @69
    @4
    c.x
    @63
    @15
    @68
    @6
    c.xp
    @63
    @14
    @67
    cA
    c.ex
    @63
    cN
    c1
    @3
    wph
    @52
    @62
    @53
    adantr
    @63
    1cnd
    @62
    @3
    cc
    wcel
    wph
    @62
    @3
    @3
    cc0
    cN
    elfzelz
    zcnd
    adantl
    addsubd
    oveq1d
    oveq1d
    oveq2d
    eqtr4d
    mpteq2dva
    oveq2d
    wph
    @2
    cS
    c.pl
    cR
    c.xp
    vk
    cvv
    @8
    cA
    @24
    srgbinom.s
    @60
    srgbinom.a
    srgbinom.m
    srgbinomlem.r
    wph
    cc0
    cN
    cfz
    ovexd
    srgbinomlem.a
    @63
    wph
    @29
    @70
    @31
    @8
    cS
    wcel
    @64
    @65
    @71
    @66
    wph
    cA
    cB
    @4
    @5
    c.pl
    cR
    cS
    c.x
    c.xp
    @3
    c.ex
    cG
    cN
    srgbinom.s
    srgbinom.m
    srgbinom.t
    srgbinom.a
    srgbinom.g
    srgbinom.e
    srgbinomlem.r
    srgbinomlem.a
    srgbinomlem.b
    srgbinomlem.c
    srgbinomlem.n
    srgbinomlem2
    syl13anc
    wph
    vk
    @2
    @9
    cvv
    cvv
    @8
    @24
    @9
    eqid
    @61
    @63
    @4
    @7
    c.x
    ovexd
    wph
    cR
    c0g
    fvexd
    fsuppmptdm
    srgsummulcr
    3eqtr2rd
    adantr
    eqtrd
end
