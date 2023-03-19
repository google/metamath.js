include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "cseq.mm"
include "cdiv.mm"
include "cexp.mm"
include "cr.mm"
include "1red.mm"
include "rpred.mm"
include "resubcld.mm"
include "adantr.mm"
include "nndivred.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "reexpcld.mm"
include "cuz.mm"
include "cn.mm"
include "elnnuz.mm"
include "sylib.mm"
include "cfz.mm"
include "wi.mm"
include "nfv.mm"
include "nfan.mm"
include "cmpt.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfmpt.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "nfel1.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "cvv.mm"
include "sselda.mm"
include "ovex.mm"
include "mptexg.mm"
include "mp1i.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "wf.mm"
include "ffvelrnda.mm"
include "simpl.mm"
include "jca.mm"
include "feq1.mm"
include "vtoclg.mm"
include "sylc.mm"
include "adantlr.mm"
include "ffvelrnd.mm"
include "fvmpt2d.mm"
include "eqeltrd.mm"
include "chvar.mm"
include "remulcl.mm"
include "adantl.mm"
include "seqcl.mm"
include "cle.mm"
include "cneg.mm"
include "caddc.mm"
include "rpcnd.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcan1d.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "1cnd.mm"
include "divcld.mm"
include "mulcld.mm"
include "negsubd.mm"
include "mulneg1d.mm"
include "3eqtr2d.mm"
include "renegcld.mm"
include "nnred.mm"
include "c3.mm"
include "3re.mm"
include "a1i.mm"
include "cc0.mm"
include "wne.mm"
include "3ne0.mm"
include "rereccld.mm"
include "1lt3.mm"
include "wb.mm"
include "0lt1.mm"
include "3pos.mm"
include "ltdiv2.mm"
include "syl222anc.mm"
include "mpbid.mm"
include "1div1e1.mm"
include "syl6breq.mm"
include "lttrd.mm"
include "nnge1d.mm"
include "ltletrd.mm"
include "ltled.mm"
include "rpregt0d.mm"
include "nngt0d.mm"
include "lediv2.mm"
include "syl121anc.mm"
include "cc.mm"
include "rpcnne0d.mm"
include "divid.mm"
include "syl.mm"
include "breqtrd.mm"
include "lenegd.mm"
include "bernneq.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "eqbrtrd.mm"
include "eqid.mm"
include "fmptdf.mm"
include "feq1d.mm"
include "mpbird.mm"
include "r19.21bi.mm"
include "an32s.mm"
include "breqtrrd.mm"
include "crp.mm"
include "addid2d.mm"
include "syl221anc.mm"
include "div1d.mm"
include "lelttrd.mm"
include "0red.mm"
include "ltaddsubd.mm"
include "elrpd.mm"
include "stoweidlem3.mm"
include "fmuldfeq.mm"
include "ex.mm"
include "ralrimi.mm"

theorem stoweidlem42
  let wph: wff ph
  let vt: setvar t
  let cB: class B
  let cP: class P
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let cE: class E
  let cF: class F
  let cM: class M
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  assume stoweidlem42.1: |- F/ i ph
  assume stoweidlem42.2: |- F/ t ph
  assume stoweidlem42.3: |- F/_ t Y
  assume stoweidlem42.4: |- P = ( f e. Y , g e. Y |-> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) )
  assume stoweidlem42.5: |- X = ( seq 1 ( P , U ) ` M )
  assume stoweidlem42.6: |- F = ( t e. T |-> ( i e. ( 1 ... M ) |-> ( ( U ` i ) ` t ) ) )
  assume stoweidlem42.7: |- Z = ( t e. T |-> ( seq 1 ( x. , ( F ` t ) ) ` M ) )
  assume stoweidlem42.8: |- ( ph -> M e. NN )
  assume stoweidlem42.9: |- ( ph -> U : ( 1 ... M ) --> Y )
  assume stoweidlem42.10: |- ( ( ph /\ i e. ( 1 ... M ) ) -> A. t e. B ( 1 - ( E / M ) ) < ( ( U ` i ) ` t ) )
  assume stoweidlem42.11: |- ( ph -> E e. RR+ )
  assume stoweidlem42.12: |- ( ph -> E < ( 1 / 3 ) )
  assume stoweidlem42.13: |- ( ( ph /\ f e. Y ) -> f : T --> RR )
  assume stoweidlem42.14: |- ( ( ph /\ f e. Y /\ g e. Y ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. Y )
  assume stoweidlem42.15: |- ( ph -> T e. _V )
  assume stoweidlem42.16: |- ( ph -> B C_ T )

  disjoint i t
  disjoint B i
  disjoint M i
  disjoint f g
  disjoint f t
  disjoint T f
  disjoint g t
  disjoint T g
  disjoint T t
  disjoint f i
  disjoint T i
  disjoint F f
  disjoint F g
  disjoint M f
  disjoint M g
  disjoint U f
  disjoint U g
  disjoint U t
  disjoint Y f
  disjoint Y g
  disjoint f ph
  disjoint g ph
  disjoint E i
  disjoint U i
  disjoint a i
  disjoint a t
  disjoint a j
  disjoint j t
  disjoint B a
  disjoint F a
  disjoint F j
  disjoint M a
  disjoint a ph
  disjoint j ph
  disjoint B j
  disjoint k x
  assert |- ( ph -> A. t e. B ( 1 - E ) < ( X ` t ) )

  proof
    wph
    c1
    cE
    cmin
    co
    #
    vt
    cv
    #
    cX
    cfv
    #
    clt
    wbr
    #
    vt
    cB
    stoweidlem42.2
    wph
    @1
    cB
    wcel
    #
    @3
    wph
    @4
    wa
    #
    @0
    @1
    cZ
    cfv
    #
    @2
    clt
    @5
    @0
    cM
    cmul
    @1
    cF
    cfv
    #
    c1
    cseq
    #
    cfv
    #
    @6
    clt
    @5
    @0
    c1
    cE
    cM
    cdiv
    co
    #
    cmin
    co
    #
    cM
    cexp
    co
    #
    @9
    wph
    @0
    cr
    wcel
    @4
    wph
    c1
    cE
    wph
    1red
    #
    wph
    cE
    stoweidlem42.11
    rpred
    #
    resubcld
    adantr
    @5
    @11
    cM
    wph
    @11
    cr
    wcel
    @4
    wph
    c1
    @10
    @13
    wph
    cE
    cM
    @14
    stoweidlem42.8
    nndivred
    #
    resubcld
    #
    adantr
    wph
    cM
    cn0
    wcel
    #
    @4
    wph
    cM
    stoweidlem42.8
    nnnn0d
    #
    adantr
    reexpcld
    @5
    va
    vj
    cmul
    cr
    @7
    c1
    cM
    wph
    cM
    c1
    cuz
    cfv
    wcel
    #
    @4
    wph
    cM
    cn
    wcel
    #
    @19
    stoweidlem42.8
    cM
    elnnuz
    sylib
    adantr
    @5
    vi
    cv
    #
    c1
    cM
    cfz
    co
    #
    wcel
    #
    wa
    #
    @21
    @7
    cfv
    #
    cr
    wcel
    #
    wi
    @5
    va
    cv
    #
    @22
    wcel
    #
    wa
    #
    @27
    @7
    cfv
    #
    cr
    wcel
    #
    wi
    vi
    va
    @29
    @31
    vi
    @5
    @28
    vi
    wph
    @4
    vi
    stoweidlem42.1
    @4
    vi
    nfv
    nfan
    #
    @28
    vi
    nfv
    nfan
    vi
    @30
    cr
    vi
    @27
    @7
    vi
    @1
    cF
    vi
    cF
    vt
    cT
    vi
    @22
    @1
    @21
    cU
    cfv
    #
    cfv
    #
    cmpt
    #
    cmpt
    stoweidlem42.6
    vi
    vt
    cT
    @35
    vi
    cT
    nfcv
    vi
    @22
    @34
    nfmpt1
    nfmpt
    nfcxfr
    vi
    @1
    nfcv
    nffv
    #
    vi
    @27
    nfcv
    nffv
    nfel1
    nfim
    @21
    @27
    wceq
    #
    @24
    @29
    @26
    @31
    @37
    @23
    @28
    @5
    @21
    @27
    @22
    eleq1
    anbi2d
    @37
    @25
    @30
    cr
    @21
    @27
    @7
    fveq2
    eleq1d
    imbi12d
    @24
    @25
    @34
    cr
    @5
    vi
    @22
    @34
    @7
    cr
    @5
    @1
    cT
    wcel
    #
    @35
    cvv
    wcel
    #
    @7
    @35
    wceq
    wph
    cB
    cT
    @1
    stoweidlem42.16
    sselda
    #
    @22
    cvv
    wcel
    @39
    @5
    c1
    cM
    cfz
    ovex
    vi
    @22
    @34
    cvv
    mptexg
    mp1i
    vt
    cT
    @35
    cvv
    cF
    stoweidlem42.6
    fvmpt2
    syl2anc
    #
    @24
    cT
    cr
    @1
    @33
    wph
    @23
    cT
    cr
    @33
    wf
    #
    @4
    wph
    @23
    wa
    #
    @33
    cY
    wcel
    #
    wph
    @44
    wa
    #
    @42
    wph
    @22
    cY
    @21
    cU
    stoweidlem42.9
    ffvelrnda
    #
    @43
    wph
    @44
    wph
    @23
    simpl
    @46
    jca
    wph
    vf
    cv
    #
    cY
    wcel
    #
    wa
    #
    cT
    cr
    @47
    wf
    #
    wi
    @45
    @42
    wi
    vf
    @33
    cY
    @47
    @33
    wceq
    #
    @49
    @45
    @50
    @42
    @51
    @48
    @44
    wph
    @47
    @33
    cY
    eleq1
    anbi2d
    cT
    cr
    @47
    @33
    feq1
    imbi12d
    stoweidlem42.13
    vtoclg
    sylc
    adantlr
    @5
    @38
    @23
    @40
    adantr
    ffvelrnd
    #
    fvmpt2d
    #
    @52
    eqeltrd
    chvar
    @27
    cr
    wcel
    vj
    cv
    #
    cr
    wcel
    wa
    @27
    @54
    cmul
    co
    cr
    wcel
    @5
    @27
    @54
    remulcl
    adantl
    seqcl
    #
    wph
    @0
    @12
    cle
    wbr
    @4
    wph
    @0
    c1
    @10
    cneg
    #
    cM
    cmul
    co
    #
    caddc
    co
    #
    @12
    cle
    wph
    @0
    c1
    @10
    cM
    cmul
    co
    #
    cmin
    co
    c1
    @59
    cneg
    #
    caddc
    co
    @58
    wph
    cE
    @59
    c1
    cmin
    wph
    @59
    cE
    wph
    cE
    cM
    wph
    cE
    stoweidlem42.11
    rpcnd
    #
    wph
    cM
    stoweidlem42.8
    nncnd
    #
    wph
    cM
    stoweidlem42.8
    nnne0d
    #
    divcan1d
    eqcomd
    oveq2d
    wph
    c1
    @59
    wph
    1cnd
    #
    wph
    @10
    cM
    wph
    cE
    cM
    @61
    @62
    @63
    divcld
    #
    @62
    mulcld
    negsubd
    wph
    @60
    @57
    c1
    caddc
    wph
    @57
    @60
    wph
    @10
    cM
    @65
    @62
    mulneg1d
    eqcomd
    oveq2d
    3eqtr2d
    wph
    @58
    c1
    @56
    caddc
    co
    #
    cM
    cexp
    co
    #
    @12
    cle
    wph
    @56
    cr
    wcel
    @17
    c1
    cneg
    @56
    cle
    wbr
    #
    @58
    @67
    cle
    wbr
    wph
    @10
    @15
    renegcld
    @18
    wph
    @10
    c1
    cle
    wbr
    @68
    wph
    @10
    cE
    cE
    cdiv
    co
    #
    c1
    cle
    wph
    cE
    cM
    cle
    wbr
    #
    @10
    @69
    cle
    wbr
    #
    wph
    cE
    cM
    @14
    wph
    cM
    stoweidlem42.8
    nnred
    #
    wph
    cE
    c1
    cM
    @14
    @13
    @72
    wph
    cE
    c1
    c3
    cdiv
    co
    #
    c1
    @14
    wph
    c3
    c3
    cr
    wcel
    #
    wph
    3re
    a1i
    #
    c3
    cc0
    wne
    wph
    3ne0
    a1i
    rereccld
    @13
    stoweidlem42.12
    wph
    @73
    c1
    c1
    cdiv
    co
    #
    c1
    clt
    wph
    c1
    c3
    clt
    wbr
    #
    @73
    @76
    clt
    wbr
    #
    @77
    wph
    1lt3
    a1i
    wph
    c1
    cr
    wcel
    #
    cc0
    c1
    clt
    wbr
    #
    @74
    cc0
    c3
    clt
    wbr
    #
    @79
    @80
    @77
    @78
    wb
    @13
    @80
    wph
    0lt1
    a1i
    #
    @75
    @81
    wph
    3pos
    a1i
    @13
    @82
    c1
    c3
    c1
    ltdiv2
    syl222anc
    mpbid
    1div1e1
    syl6breq
    lttrd
    #
    wph
    cM
    stoweidlem42.8
    nnge1d
    #
    ltletrd
    ltled
    wph
    cE
    cr
    wcel
    cc0
    cE
    clt
    wbr
    wa
    #
    cM
    cr
    wcel
    #
    cc0
    cM
    clt
    wbr
    #
    @85
    @70
    @71
    wb
    wph
    cE
    stoweidlem42.11
    rpregt0d
    #
    @72
    wph
    cM
    stoweidlem42.8
    nngt0d
    #
    @88
    cE
    cM
    cE
    lediv2
    syl121anc
    mpbid
    wph
    cE
    cc
    wcel
    cE
    cc0
    wne
    wa
    @69
    c1
    wceq
    wph
    cE
    stoweidlem42.11
    rpcnne0d
    cE
    divid
    syl
    breqtrd
    wph
    @10
    c1
    @15
    @13
    lenegd
    mpbid
    @56
    cM
    bernneq
    syl3anc
    wph
    @66
    @11
    cM
    cexp
    wph
    c1
    @10
    @64
    @65
    negsubd
    oveq1d
    breqtrd
    eqbrtrd
    adantr
    @5
    @11
    vi
    @7
    cM
    @8
    @36
    @32
    @8
    eqid
    wph
    @20
    @4
    stoweidlem42.8
    adantr
    @5
    @22
    cr
    @7
    wf
    @22
    cr
    @35
    wf
    @5
    vi
    @22
    @34
    cr
    @35
    @32
    @52
    @35
    eqid
    fmptdf
    @5
    @22
    cr
    @7
    @35
    @41
    feq1d
    mpbird
    @24
    @11
    @34
    @25
    clt
    wph
    @23
    @4
    @11
    @34
    clt
    wbr
    #
    @43
    @90
    vt
    cB
    stoweidlem42.10
    r19.21bi
    an32s
    @53
    breqtrrd
    wph
    @11
    crp
    wcel
    @4
    wph
    @11
    @16
    wph
    cc0
    @10
    caddc
    co
    #
    c1
    clt
    wbr
    cc0
    @11
    clt
    wbr
    wph
    @91
    @10
    c1
    clt
    wph
    @10
    @65
    addid2d
    wph
    @10
    cE
    c1
    @15
    @14
    @13
    wph
    @10
    cE
    c1
    cdiv
    co
    #
    cE
    cle
    wph
    c1
    cM
    cle
    wbr
    #
    @10
    @92
    cle
    wbr
    #
    @84
    wph
    @79
    @80
    @86
    @87
    @85
    @93
    @94
    wb
    @13
    @82
    @72
    @89
    @88
    c1
    cM
    cE
    lediv2
    syl221anc
    mpbid
    wph
    cE
    @61
    div1d
    breqtrd
    @83
    lelttrd
    eqbrtrd
    wph
    cc0
    @10
    c1
    wph
    0red
    @15
    @13
    ltaddsubd
    mpbid
    elrpd
    adantr
    stoweidlem3
    lelttrd
    @5
    @38
    @9
    cr
    wcel
    @6
    @9
    wceq
    @40
    @55
    vt
    cT
    @9
    cr
    cZ
    stoweidlem42.7
    fvmpt2
    syl2anc
    breqtrrd
    @5
    wph
    @38
    @2
    @6
    wceq
    wph
    @4
    simpl
    @40
    wph
    vt
    cP
    cT
    cU
    vf
    vg
    vi
    cF
    cM
    cX
    cY
    cZ
    stoweidlem42.1
    stoweidlem42.3
    stoweidlem42.4
    stoweidlem42.5
    stoweidlem42.6
    stoweidlem42.7
    stoweidlem42.15
    stoweidlem42.8
    stoweidlem42.9
    stoweidlem42.13
    stoweidlem42.14
    fmuldfeq
    syl2anc
    breqtrrd
    ex
    ralrimi
end
