include "cr.mm"
include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cdiv.mm"
include "cof.mm"
include "co.mm"
include "crp.mm"
include "cc0.mm"
include "cfzo.mm"
include "cv.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "csn.mm"
include "caddc.mm"
include "cmpt.mm"
include "crli.mm"
include "cfz.mm"
include "cc.mm"
include "cvv.mm"
include "wf.mm"
include "wfn.mm"
include "plyf.mm"
include "ffn.mm"
include "syl.mm"
include "wral.mm"
include "ovex.mm"
include "rgenw.mm"
include "fnmpt.mm"
include "mp1i.mm"
include "cnex.mm"
include "a1i.mm"
include "reex.mm"
include "rpssre.mm"
include "ssexi.mm"
include "wss.mm"
include "cin.mm"
include "wceq.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "coeid2.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "adantl.mm"
include "offval.mm"
include "wa.mm"
include "fzfid.mm"
include "sselda.mm"
include "cn0.mm"
include "cdgr.mm"
include "dgrcl.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "expcld.mm"
include "coef3.mm"
include "ad2antrr.mm"
include "elfznn0.mm"
include "ffvelrnd.mm"
include "mulcld.mm"
include "wne.mm"
include "rpne0.mm"
include "cz.mm"
include "nn0zd.mm"
include "expne0d.mm"
include "fsumdivc.mm"
include "c0.mm"
include "c1.mm"
include "fzodisj.mm"
include "fzosn.mm"
include "ineq2d.mm"
include "syl5reqr.mm"
include "cun.mm"
include "fzval3.mm"
include "cuz.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "fzosplitsn.mm"
include "eqtrd.mm"
include "divcld.mm"
include "fsumsplit.mm"
include "mpteq2dva.mm"
include "sumex.mm"
include "cfn.mm"
include "fzofi.mm"
include "ovexd.mm"
include "elfzonn0.mm"
include "ad2antlr.mm"
include "adantlr.mm"
include "divassd.mm"
include "fvexd.mm"
include "wbr.mm"
include "rlimconst.mm"
include "sylancr.mm"
include "cmin.mm"
include "ccxp.mm"
include "cneg.mm"
include "zsubcld.mm"
include "cxpexpzd.mm"
include "oveq2d.mm"
include "expnegd.mm"
include "zcnd.mm"
include "nn0cnd.mm"
include "negsubdi2d.mm"
include "3eqtr2d.mm"
include "expsubd.mm"
include "clt.mm"
include "nn0red.mm"
include "elfzolt2.mm"
include "difrp.mm"
include "biimpa.mm"
include "syl21anc.mm"
include "cxplim.mm"
include "eqbrtrrd.mm"
include "rlimmul.mm"
include "mul01d.mm"
include "breqtrd.mm"
include "eqbrtrd.mm"
include "fsumrlim.mm"
include "wo.mm"
include "olcd.mm"
include "sumz.mm"
include "fveq2.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "sumsn.mm"
include "syl2anc.mm"
include "divcan4d.mm"
include "rlimadd.mm"
include "addid2d.mm"
include "syl6eqr.mm"

theorem signsplypnf
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let vk: setvar k
  assume signsply0.d: |- D = ( deg ` F )
  assume signsply0.c: |- C = ( coeff ` F )
  assume signsply0.b: |- B = ( C ` D )
  assume signsplypnf.g: |- G = ( x e. RR+ |-> ( x ^ D ) )

  disjoint C x
  disjoint D x
  disjoint F x
  disjoint G x
  disjoint k x
  disjoint C k
  disjoint D k
  disjoint F k
  assert |- ( F e. ( Poly ` RR ) -> ( F oF / G ) ~~>r B )

  proof
    cF
    cr
    cply
    cfv
    wcel
    #
    cF
    cG
    cdiv
    cof
    co
    #
    vx
    crp
    cc0
    cD
    cfzo
    co
    #
    vk
    cv
    #
    cC
    cfv
    #
    vx
    cv
    #
    @3
    cexp
    co
    #
    cmul
    co
    #
    @5
    cD
    cexp
    co
    #
    cdiv
    co
    #
    vk
    csu
    #
    cD
    csn
    #
    @9
    vk
    csu
    #
    caddc
    co
    #
    cmpt
    #
    cB
    crli
    @0
    @1
    vx
    crp
    cc0
    cD
    cfz
    co
    #
    @7
    vk
    csu
    #
    @8
    cdiv
    co
    #
    cmpt
    @14
    @0
    vx
    cc
    crp
    @16
    @8
    cdiv
    crp
    cF
    cG
    cvv
    cvv
    @0
    cc
    cc
    cF
    wf
    cF
    cc
    wfn
    cr
    cF
    plyf
    cc
    cc
    cF
    ffn
    syl
    @8
    cvv
    wcel
    #
    vx
    crp
    wral
    cG
    crp
    wfn
    @0
    @18
    vx
    crp
    @5
    cD
    cexp
    ovex
    #
    rgenw
    vx
    crp
    @8
    cG
    cvv
    signsplypnf.g
    fnmpt
    mp1i
    cc
    cvv
    wcel
    @0
    cnex
    a1i
    crp
    cvv
    wcel
    @0
    crp
    cr
    reex
    rpssre
    ssexi
    a1i
    crp
    cc
    wss
    #
    cc
    crp
    cin
    crp
    wceq
    crp
    cr
    cc
    rpssre
    ax-resscn
    sstri
    #
    crp
    cc
    sseqin2
    mpbi
    cC
    cr
    vk
    cF
    cD
    @5
    signsply0.c
    signsply0.d
    coeid2
    @5
    crp
    wcel
    #
    @5
    cG
    cfv
    @8
    wceq
    #
    @0
    @22
    @18
    @23
    @19
    vx
    crp
    @8
    cvv
    cG
    signsplypnf.g
    fvmpt2
    mpan2
    adantl
    offval
    @0
    vx
    crp
    @17
    @13
    @0
    @22
    wa
    #
    @17
    @15
    @9
    vk
    csu
    @13
    @24
    @15
    @7
    @8
    vk
    @24
    cc0
    cD
    fzfid
    #
    @24
    @5
    cD
    @0
    crp
    cc
    @5
    @20
    @0
    @21
    a1i
    sselda
    #
    @0
    cD
    cn0
    wcel
    #
    @22
    @0
    cD
    cF
    cdgr
    cfv
    cn0
    signsply0.d
    cr
    cF
    dgrcl
    syl5eqel
    #
    adantr
    #
    expcld
    #
    @24
    @3
    @15
    wcel
    #
    wa
    #
    @4
    @6
    @32
    cn0
    cc
    @3
    cC
    @0
    cn0
    cc
    cC
    wf
    #
    @22
    @31
    cC
    cr
    cF
    signsply0.c
    coef3
    #
    ad2antrr
    @31
    @3
    cn0
    wcel
    #
    @24
    @3
    cD
    elfznn0
    adantl
    #
    ffvelrnd
    @32
    @5
    @3
    @24
    @5
    cc
    wcel
    #
    @31
    @26
    adantr
    #
    @36
    expcld
    mulcld
    #
    @24
    @5
    cD
    @26
    @22
    @5
    cc0
    wne
    #
    @0
    @5
    rpne0
    #
    adantl
    #
    @0
    cD
    cz
    wcel
    #
    @22
    @0
    cD
    @28
    nn0zd
    #
    adantr
    #
    expne0d
    #
    fsumdivc
    @24
    @2
    @11
    @9
    @15
    vk
    @24
    @43
    @2
    @11
    cin
    #
    c0
    wceq
    @45
    @43
    c0
    @2
    cD
    cD
    c1
    caddc
    co
    #
    cfzo
    co
    #
    cin
    @47
    cc0
    cD
    @48
    fzodisj
    @43
    @49
    @11
    @2
    cD
    fzosn
    ineq2d
    syl5reqr
    syl
    @0
    @15
    @2
    @11
    cun
    #
    wceq
    @22
    @0
    @15
    cc0
    @48
    cfzo
    co
    #
    @50
    @0
    @43
    @15
    @51
    wceq
    @44
    cc0
    cD
    fzval3
    syl
    @0
    cD
    cc0
    cuz
    cfv
    #
    wcel
    @51
    @50
    wceq
    @0
    cD
    cn0
    @52
    @28
    nn0uz
    syl6eleq
    cc0
    cD
    fzosplitsn
    syl
    eqtrd
    adantr
    @25
    @32
    @7
    @8
    @39
    @24
    @8
    cc
    wcel
    #
    @31
    @30
    adantr
    @32
    @5
    cD
    @38
    @24
    @40
    @31
    @42
    adantr
    @24
    @43
    @31
    @45
    adantr
    expne0d
    divcld
    fsumsplit
    eqtrd
    mpteq2dva
    eqtrd
    @0
    @14
    cc0
    cD
    cC
    cfv
    #
    caddc
    co
    #
    cB
    crli
    @0
    vx
    crp
    @10
    @12
    cc0
    @54
    cvv
    @10
    cvv
    wcel
    @24
    @2
    @9
    vk
    sumex
    a1i
    @12
    cvv
    wcel
    @24
    @11
    @9
    vk
    sumex
    a1i
    @0
    vx
    crp
    @10
    cmpt
    @2
    cc0
    vk
    csu
    #
    cc0
    crli
    @0
    vx
    crp
    @2
    @9
    cc0
    vk
    cvv
    crp
    cr
    wss
    #
    @0
    rpssre
    a1i
    @2
    cfn
    wcel
    #
    @0
    cc0
    cD
    fzofi
    a1i
    #
    @0
    @22
    @3
    @2
    wcel
    #
    wa
    wa
    @7
    @8
    cdiv
    ovexd
    @0
    @60
    wa
    #
    vx
    crp
    @9
    cmpt
    vx
    crp
    @4
    @6
    @8
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    #
    cc0
    crli
    @61
    vx
    crp
    @9
    @63
    @61
    @22
    wa
    #
    @4
    @6
    @8
    @65
    cn0
    cc
    @3
    cC
    @0
    @33
    @60
    @22
    @34
    ad2antrr
    @60
    @35
    @0
    @22
    @3
    cD
    elfzonn0
    #
    ad2antlr
    #
    ffvelrnd
    @65
    @5
    @3
    @0
    @22
    @37
    @60
    @26
    adantlr
    #
    @67
    expcld
    @0
    @22
    @53
    @60
    @30
    adantlr
    @65
    @5
    cD
    @68
    @22
    @40
    @61
    @41
    adantl
    #
    @0
    @22
    @43
    @60
    @45
    adantlr
    #
    expne0d
    divassd
    mpteq2dva
    @61
    @64
    @4
    cc0
    cmul
    co
    cc0
    crli
    @61
    vx
    crp
    @4
    @62
    @4
    cc0
    cvv
    @65
    @3
    cC
    fvexd
    @65
    @6
    @8
    cdiv
    ovexd
    @61
    @57
    @4
    cc
    wcel
    vx
    crp
    @4
    cmpt
    @4
    crli
    wbr
    rpssre
    @61
    cn0
    cc
    @3
    cC
    @0
    @33
    @60
    @34
    adantr
    @60
    @35
    @0
    @66
    adantl
    #
    ffvelrnd
    #
    vx
    crp
    @4
    rlimconst
    sylancr
    @61
    vx
    crp
    c1
    @5
    cD
    @3
    cmin
    co
    #
    ccxp
    co
    #
    cdiv
    co
    #
    cmpt
    #
    vx
    crp
    @62
    cmpt
    cc0
    crli
    @61
    vx
    crp
    @75
    @62
    @65
    @75
    @5
    @3
    cD
    cmin
    co
    #
    cexp
    co
    #
    @62
    @65
    @75
    c1
    @5
    @73
    cexp
    co
    #
    cdiv
    co
    @5
    @73
    cneg
    #
    cexp
    co
    @78
    @65
    @74
    @79
    c1
    cdiv
    @65
    @5
    @73
    @68
    @69
    @65
    cD
    @3
    @70
    @65
    @3
    @67
    nn0zd
    #
    zsubcld
    #
    cxpexpzd
    oveq2d
    @65
    @5
    @73
    @68
    @69
    @82
    expnegd
    @65
    @80
    @77
    @5
    cexp
    @65
    cD
    @3
    @65
    cD
    @70
    zcnd
    @65
    @3
    @67
    nn0cnd
    negsubdi2d
    oveq2d
    3eqtr2d
    @65
    @5
    @3
    cD
    @68
    @69
    @70
    @81
    expsubd
    eqtrd
    mpteq2dva
    @61
    @73
    crp
    wcel
    #
    @76
    cc0
    crli
    wbr
    @61
    @3
    cr
    wcel
    #
    cD
    cr
    wcel
    #
    @3
    cD
    clt
    wbr
    #
    @83
    @61
    @3
    @71
    nn0red
    @61
    cD
    @0
    @27
    @60
    @28
    adantr
    nn0red
    @60
    @86
    @0
    @3
    cc0
    cD
    elfzolt2
    adantl
    @84
    @85
    wa
    @86
    @83
    @3
    cD
    difrp
    biimpa
    syl21anc
    @73
    vx
    cxplim
    syl
    eqbrtrrd
    rlimmul
    @61
    @4
    @72
    mul01d
    breqtrd
    eqbrtrd
    fsumrlim
    @0
    @2
    @52
    wss
    #
    @58
    wo
    @56
    cc0
    wceq
    @0
    @58
    @87
    @59
    olcd
    @2
    vk
    cc0
    sumz
    syl
    breqtrd
    @0
    vx
    crp
    @12
    cmpt
    vx
    crp
    @54
    cmpt
    #
    @54
    crli
    @0
    vx
    crp
    @12
    @54
    @24
    @12
    @54
    @8
    cmul
    co
    #
    @8
    cdiv
    co
    #
    @54
    @24
    @27
    @90
    cc
    wcel
    @12
    @90
    wceq
    @29
    @24
    @89
    @8
    @24
    @54
    @8
    @0
    @54
    cc
    wcel
    #
    @22
    @0
    cn0
    cc
    cD
    cC
    @34
    @28
    ffvelrnd
    #
    adantr
    #
    @30
    mulcld
    @30
    @46
    divcld
    @9
    @90
    vk
    cD
    cn0
    @3
    cD
    wceq
    #
    @7
    @89
    @8
    cdiv
    @94
    @4
    @54
    @6
    @8
    cmul
    @3
    cD
    cC
    fveq2
    @3
    cD
    @5
    cexp
    oveq2
    oveq12d
    oveq1d
    sumsn
    syl2anc
    @24
    @54
    @8
    @93
    @30
    @46
    divcan4d
    eqtrd
    mpteq2dva
    @0
    @57
    @91
    @88
    @54
    crli
    wbr
    rpssre
    @92
    vx
    crp
    @54
    rlimconst
    sylancr
    eqbrtrd
    rlimadd
    @0
    @55
    @54
    cB
    @0
    @54
    @92
    addid2d
    signsply0.b
    syl6eqr
    breqtrd
    eqbrtrd
end
