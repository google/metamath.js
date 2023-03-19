include "caddc.mm"
include "cof.mm"
include "co.mm"
include "cc.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "cfv.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cvv.mm"
include "wcel.mm"
include "cnex.mm"
include "a1i.mm"
include "wa.mm"
include "sumex.mm"
include "offval2.mm"
include "fzfid.mm"
include "cn0.mm"
include "elfznn0.mm"
include "wf.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "expcl.mm"
include "adantll.mm"
include "mulcld.mm"
include "sylan2.mm"
include "fsumadd.mm"
include "wceq.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "nn0ex.mm"
include "inidm.mm"
include "eqidd.mm"
include "ofval.mm"
include "adantlr.mm"
include "oveq1d.mm"
include "adddird.mm"
include "eqtrd.mm"
include "sumeq2dv.mm"
include "wss.mm"
include "cuz.mm"
include "cz.mm"
include "nn0zd.mm"
include "ifcld.mm"
include "cr.mm"
include "nn0red.mm"
include "max1.mm"
include "syl2anc.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "fzss2.mm"
include "cdif.mm"
include "csn.mm"
include "c1.mm"
include "cima.mm"
include "wn.mm"
include "eldifn.mm"
include "adantl.mm"
include "cun.mm"
include "wo.mm"
include "eldifi.mm"
include "cmin.mm"
include "nn0uz.mm"
include "peano2nn0.mm"
include "syl6eleq.mm"
include "uzsplit.mm"
include "syl5eq.mm"
include "nn0cnd.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "uneq1d.mm"
include "ad2antrr.mm"
include "eleqtrd.mm"
include "elun.mm"
include "sylib.mm"
include "ord.mm"
include "mpd.mm"
include "wi.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "ssun2.mm"
include "syl5sseqr.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "funfvima2.mm"
include "elsni.mm"
include "mul02d.mm"
include "fsumss.mm"
include "max2.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"

theorem plyaddlem1
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vn: setvar n
  assume plyaddlem.1: |- ( ph -> F e. ( Poly ` S ) )
  assume plyaddlem.2: |- ( ph -> G e. ( Poly ` S ) )
  assume plyaddlem.m: |- ( ph -> M e. NN0 )
  assume plyaddlem.n: |- ( ph -> N e. NN0 )
  assume plyaddlem.a: |- ( ph -> A : NN0 --> CC )
  assume plyaddlem.b: |- ( ph -> B : NN0 --> CC )
  assume plyaddlem.a2: |- ( ph -> ( A " ( ZZ>= ` ( M + 1 ) ) ) = { 0 } )
  assume plyaddlem.b2: |- ( ph -> ( B " ( ZZ>= ` ( N + 1 ) ) ) = { 0 } )
  assume plyaddlem.f: |- ( ph -> F = ( z e. CC |-> sum_ k e. ( 0 ... M ) ( ( A ` k ) x. ( z ^ k ) ) ) )
  assume plyaddlem.g: |- ( ph -> G = ( z e. CC |-> sum_ k e. ( 0 ... N ) ( ( B ` k ) x. ( z ^ k ) ) ) )

  disjoint B k
  disjoint M k
  disjoint N k
  disjoint k z
  disjoint k ph
  disjoint ph z
  disjoint m n
  disjoint A m
  disjoint A n
  disjoint k m
  disjoint k n
  disjoint B m
  disjoint B n
  disjoint M m
  disjoint M n
  disjoint N m
  disjoint N n
  disjoint m z
  disjoint m ph
  disjoint n z
  disjoint n ph
  assert |- ( ph -> ( F oF + G ) = ( z e. CC |-> sum_ k e. ( 0 ... if ( M <_ N , N , M ) ) ( ( ( A oF + B ) ` k ) x. ( z ^ k ) ) ) )

  proof
    wph
    cF
    cG
    caddc
    cof
    #
    co
    vz
    cc
    cc0
    cM
    cfz
    co
    #
    vk
    cv
    #
    cA
    cfv
    #
    vz
    cv
    #
    @2
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cc0
    cN
    cfz
    co
    #
    @2
    cB
    cfv
    #
    @5
    cmul
    co
    #
    vk
    csu
    #
    caddc
    co
    #
    cmpt
    vz
    cc
    cc0
    cM
    cN
    cle
    wbr
    #
    cN
    cM
    cif
    #
    cfz
    co
    #
    @2
    cA
    cB
    @0
    co
    cfv
    #
    @5
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    wph
    vz
    cc
    @7
    @11
    caddc
    cF
    cG
    cvv
    cvv
    cvv
    cc
    cvv
    wcel
    wph
    cnex
    a1i
    @7
    cvv
    wcel
    wph
    @4
    cc
    wcel
    #
    wa
    #
    @1
    @6
    vk
    sumex
    a1i
    @11
    cvv
    wcel
    @20
    @8
    @10
    vk
    sumex
    a1i
    plyaddlem.f
    plyaddlem.g
    offval2
    wph
    vz
    cc
    @18
    @12
    @20
    @15
    @6
    @10
    caddc
    co
    #
    vk
    csu
    @15
    @6
    vk
    csu
    #
    @15
    @10
    vk
    csu
    #
    caddc
    co
    @18
    @12
    @20
    @15
    @6
    @10
    vk
    @20
    cc0
    @14
    fzfid
    #
    @2
    @15
    wcel
    #
    @20
    @2
    cn0
    wcel
    #
    @6
    cc
    wcel
    #
    @2
    @14
    elfznn0
    #
    @20
    @26
    wa
    #
    @3
    @5
    @20
    cn0
    cc
    @2
    cA
    wph
    cn0
    cc
    cA
    wf
    #
    @19
    plyaddlem.a
    adantr
    ffvelrnda
    #
    @19
    @26
    @5
    cc
    wcel
    #
    wph
    @4
    @2
    expcl
    adantll
    #
    mulcld
    #
    sylan2
    @25
    @20
    @26
    @10
    cc
    wcel
    #
    @28
    @29
    @9
    @5
    @20
    cn0
    cc
    @2
    cB
    wph
    cn0
    cc
    cB
    wf
    #
    @19
    plyaddlem.b
    adantr
    ffvelrnda
    #
    @33
    mulcld
    #
    sylan2
    fsumadd
    @20
    @15
    @17
    @21
    vk
    @25
    @20
    @26
    @17
    @21
    wceq
    @28
    @29
    @17
    @3
    @9
    caddc
    co
    #
    @5
    cmul
    co
    @21
    @29
    @16
    @39
    @5
    cmul
    wph
    @26
    @16
    @39
    wceq
    @19
    wph
    cn0
    cn0
    @3
    @9
    caddc
    cn0
    cA
    cB
    cvv
    cvv
    @2
    wph
    @30
    cA
    cn0
    wfn
    plyaddlem.a
    cn0
    cc
    cA
    ffn
    syl
    wph
    @36
    cB
    cn0
    wfn
    plyaddlem.b
    cn0
    cc
    cB
    ffn
    syl
    cn0
    cvv
    wcel
    wph
    nn0ex
    a1i
    #
    @40
    cn0
    inidm
    wph
    @26
    wa
    #
    @3
    eqidd
    @41
    @9
    eqidd
    ofval
    adantlr
    oveq1d
    @29
    @3
    @9
    @5
    @31
    @37
    @33
    adddird
    eqtrd
    sylan2
    sumeq2dv
    @20
    @7
    @22
    @11
    @23
    caddc
    @20
    @1
    @15
    @6
    vk
    wph
    @1
    @15
    wss
    #
    @19
    wph
    @14
    cM
    cuz
    cfv
    wcel
    #
    @42
    wph
    cM
    cz
    wcel
    @14
    cz
    wcel
    #
    cM
    @14
    cle
    wbr
    #
    @43
    wph
    cM
    plyaddlem.m
    nn0zd
    wph
    @14
    wph
    @13
    cN
    cM
    cn0
    plyaddlem.n
    plyaddlem.m
    ifcld
    nn0zd
    #
    wph
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @45
    wph
    cM
    plyaddlem.m
    nn0red
    #
    wph
    cN
    plyaddlem.n
    nn0red
    #
    cM
    cN
    max1
    syl2anc
    cM
    @14
    eluz2
    syl3anbrc
    cM
    cc0
    @14
    fzss2
    syl
    adantr
    @2
    @1
    wcel
    #
    @20
    @26
    @27
    @2
    cM
    elfznn0
    @34
    sylan2
    @20
    @2
    @15
    @1
    cdif
    wcel
    #
    wa
    #
    @6
    cc0
    @5
    cmul
    co
    #
    cc0
    @53
    @3
    cc0
    @5
    cmul
    @53
    @3
    cc0
    csn
    #
    wcel
    @3
    cc0
    wceq
    @53
    @3
    cA
    cM
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    cima
    #
    @55
    @53
    @2
    @57
    wcel
    #
    @3
    @58
    wcel
    #
    @53
    @51
    wn
    #
    @59
    @52
    @61
    @20
    @2
    @15
    @1
    eldifn
    adantl
    @53
    @51
    @59
    @53
    @2
    @1
    @57
    cun
    #
    wcel
    @51
    @59
    wo
    @53
    @2
    cn0
    @62
    @52
    @26
    @20
    @52
    @25
    @26
    @2
    @15
    @1
    eldifi
    @28
    syl
    #
    adantl
    wph
    cn0
    @62
    wceq
    @19
    @52
    wph
    cn0
    cc0
    @56
    c1
    cmin
    co
    #
    cfz
    co
    #
    @57
    cun
    #
    @62
    wph
    cn0
    cc0
    cuz
    cfv
    #
    @66
    nn0uz
    wph
    @56
    @67
    wcel
    @67
    @66
    wceq
    wph
    @56
    cn0
    @67
    wph
    cM
    cn0
    wcel
    @56
    cn0
    wcel
    plyaddlem.m
    cM
    peano2nn0
    syl
    nn0uz
    syl6eleq
    cc0
    @56
    uzsplit
    syl
    syl5eq
    #
    wph
    @65
    @1
    @57
    wph
    @64
    cM
    cc0
    cfz
    wph
    cM
    cc
    wcel
    c1
    cc
    wcel
    #
    @64
    cM
    wceq
    wph
    cM
    plyaddlem.m
    nn0cnd
    ax-1cn
    cM
    c1
    pncan
    sylancl
    oveq2d
    uneq1d
    eqtrd
    ad2antrr
    eleqtrd
    @2
    @1
    @57
    elun
    sylib
    ord
    mpd
    wph
    @59
    @60
    wi
    #
    @19
    @52
    wph
    cA
    wfun
    #
    @57
    cA
    cdm
    #
    wss
    @70
    wph
    @30
    @71
    plyaddlem.a
    cn0
    cc
    cA
    ffun
    syl
    wph
    @57
    cn0
    @72
    wph
    @66
    @57
    cn0
    @57
    @65
    ssun2
    @68
    syl5sseqr
    wph
    @30
    @72
    cn0
    wceq
    plyaddlem.a
    cn0
    cc
    cA
    fdm
    syl
    sseqtr4d
    @57
    @2
    cA
    funfvima2
    syl2anc
    ad2antrr
    mpd
    wph
    @58
    @55
    wceq
    @19
    @52
    plyaddlem.a2
    ad2antrr
    eleqtrd
    @3
    cc0
    elsni
    syl
    oveq1d
    @53
    @5
    @52
    @20
    @26
    @32
    @63
    @33
    sylan2
    mul02d
    eqtrd
    @24
    fsumss
    @20
    @8
    @15
    @10
    vk
    wph
    @8
    @15
    wss
    #
    @19
    wph
    @14
    cN
    cuz
    cfv
    wcel
    #
    @73
    wph
    cN
    cz
    wcel
    @44
    cN
    @14
    cle
    wbr
    #
    @74
    wph
    cN
    plyaddlem.n
    nn0zd
    @46
    wph
    @47
    @48
    @75
    @49
    @50
    cM
    cN
    max2
    syl2anc
    cN
    @14
    eluz2
    syl3anbrc
    cN
    cc0
    @14
    fzss2
    syl
    adantr
    @2
    @8
    wcel
    #
    @20
    @26
    @35
    @2
    cN
    elfznn0
    @38
    sylan2
    @20
    @2
    @15
    @8
    cdif
    wcel
    #
    wa
    #
    @10
    @54
    cc0
    @78
    @9
    cc0
    @5
    cmul
    @78
    @9
    @55
    wcel
    @9
    cc0
    wceq
    @78
    @9
    cB
    cN
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    cima
    #
    @55
    @78
    @2
    @80
    wcel
    #
    @9
    @81
    wcel
    #
    @78
    @76
    wn
    #
    @82
    @77
    @84
    @20
    @2
    @15
    @8
    eldifn
    adantl
    @78
    @76
    @82
    @78
    @2
    @8
    @80
    cun
    #
    wcel
    @76
    @82
    wo
    @78
    @2
    cn0
    @85
    @77
    @26
    @20
    @77
    @25
    @26
    @2
    @15
    @8
    eldifi
    @28
    syl
    #
    adantl
    wph
    cn0
    @85
    wceq
    @19
    @77
    wph
    cn0
    cc0
    @79
    c1
    cmin
    co
    #
    cfz
    co
    #
    @80
    cun
    #
    @85
    wph
    cn0
    @67
    @89
    nn0uz
    wph
    @79
    @67
    wcel
    @67
    @89
    wceq
    wph
    @79
    cn0
    @67
    wph
    cN
    cn0
    wcel
    @79
    cn0
    wcel
    plyaddlem.n
    cN
    peano2nn0
    syl
    nn0uz
    syl6eleq
    cc0
    @79
    uzsplit
    syl
    syl5eq
    #
    wph
    @88
    @8
    @80
    wph
    @87
    cN
    cc0
    cfz
    wph
    cN
    cc
    wcel
    @69
    @87
    cN
    wceq
    wph
    cN
    plyaddlem.n
    nn0cnd
    ax-1cn
    cN
    c1
    pncan
    sylancl
    oveq2d
    uneq1d
    eqtrd
    ad2antrr
    eleqtrd
    @2
    @8
    @80
    elun
    sylib
    ord
    mpd
    wph
    @82
    @83
    wi
    #
    @19
    @77
    wph
    cB
    wfun
    #
    @80
    cB
    cdm
    #
    wss
    @91
    wph
    @36
    @92
    plyaddlem.b
    cn0
    cc
    cB
    ffun
    syl
    wph
    @80
    cn0
    @93
    wph
    @89
    @80
    cn0
    @80
    @88
    ssun2
    @90
    syl5sseqr
    wph
    @36
    @93
    cn0
    wceq
    plyaddlem.b
    cn0
    cc
    cB
    fdm
    syl
    sseqtr4d
    @80
    @2
    cB
    funfvima2
    syl2anc
    ad2antrr
    mpd
    wph
    @81
    @55
    wceq
    @19
    @77
    plyaddlem.b2
    ad2antrr
    eleqtrd
    @9
    cc0
    elsni
    syl
    oveq1d
    @78
    @5
    @77
    @20
    @26
    @32
    @86
    @33
    sylan2
    mul02d
    eqtrd
    @24
    fsumss
    oveq12d
    3eqtr4d
    mpteq2dva
    eqtr4d
end
