include "cprod.mm"
include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "cif.mm"
include "cmpt.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "w3a.mm"
include "cfz.mm"
include "co.mm"
include "wf1o.mm"
include "cn.mm"
include "csb.mm"
include "wceq.mm"
include "wo.mm"
include "cio.mm"
include "df-prod.mm"
include "cvv.mm"
include "fvex.mm"
include "wb.mm"
include "wmo.mm"
include "wi.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfif.mm"
include "weq.mm"
include "eleq1.mm"
include "csbeq1a.mm"
include "ifbieq1d.mm"
include "cbvmpt.mm"
include "cc.mm"
include "wral.mm"
include "ralrimiva.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "rspc.mm"
include "mpan9.mm"
include "fveq2.mm"
include "csbeq1d.mm"
include "csbco.mm"
include "syl6eqr.mm"
include "cbvmptv.mm"
include "prodmo.mm"
include "wf.mm"
include "f1of.mm"
include "syl.mm"
include "ovex.mm"
include "fex.mm"
include "sylancl.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "elfznn.mm"
include "adantl.mm"
include "syl6eqelr.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "nffvmpt1.mm"
include "nfeq2.mm"
include "eqeq12d.mm"
include "seqfveq.mm"
include "jca.mm"
include "f1oeq1.mm"
include "fveq1.mm"
include "csbie.mm"
include "syl6eq.mm"
include "mpteq2dv.mm"
include "seqeq3d.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "sylc.mm"
include "oveq2.mm"
include "f1oeq2.mm"
include "exbidv.mm"
include "rspcev.mm"
include "olcd.mm"
include "breq2.mm"
include "3anbi3d.mm"
include "rexbidv.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "orbi12d.mm"
include "moi2.mm"
include "mpanl1.mm"
include "ancom2s.mm"
include "expr.mm"
include "syl5ibrcom.mm"
include "impbid.mm"
include "adantr.mm"
include "iota5.mm"
include "mpan2.mm"
include "syl5eq.mm"

theorem fprod
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cM: class M
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  assume fprod.1: |- ( k = ( F ` n ) -> B = C )
  assume fprod.2: |- ( ph -> M e. NN )
  assume fprod.3: |- ( ph -> F : ( 1 ... M ) -1-1-onto-> A )
  assume fprod.4: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume fprod.5: |- ( ( ph /\ n e. ( 1 ... M ) ) -> ( G ` n ) = C )

  disjoint A k
  disjoint A n
  disjoint B n
  disjoint C k
  disjoint F k
  disjoint F n
  disjoint G k
  disjoint G n
  disjoint k n
  disjoint k ph
  disjoint M k
  disjoint M n
  disjoint n ph
  disjoint A f
  disjoint A i
  disjoint A j
  disjoint A m
  disjoint A x
  disjoint A y
  disjoint B f
  disjoint B i
  disjoint B j
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint C f
  disjoint F f
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f ph
  disjoint f x
  disjoint f y
  disjoint G f
  disjoint G m
  disjoint G x
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i ph
  disjoint i x
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j ph
  disjoint j x
  disjoint k m
  disjoint k x
  disjoint k y
  disjoint M f
  disjoint M m
  disjoint m n
  disjoint m ph
  disjoint m x
  disjoint M x
  disjoint m y
  disjoint n x
  disjoint n y
  disjoint ph x
  disjoint x y
  assert |- ( ph -> prod_ k e. A B = ( seq 1 ( x. , G ) ` M ) )

  proof
    wph
    cA
    cB
    vk
    cprod
    cA
    vm
    cv
    #
    cuz
    cfv
    #
    wss
    #
    vy
    cv
    #
    cc0
    wne
    cmul
    vk
    cz
    vk
    cv
    #
    cA
    wcel
    #
    cB
    c1
    cif
    #
    cmpt
    #
    vn
    cv
    #
    cseq
    @3
    cli
    wbr
    wa
    vy
    wex
    vn
    @1
    wrex
    #
    cmul
    @7
    @0
    cseq
    #
    vx
    cv
    #
    cli
    wbr
    #
    w3a
    #
    vm
    cz
    wrex
    #
    c1
    @0
    cfz
    co
    #
    cA
    vf
    cv
    #
    wf1o
    #
    @11
    @0
    cmul
    vn
    cn
    vk
    @8
    @16
    cfv
    #
    cB
    csb
    #
    cmpt
    #
    c1
    cseq
    #
    cfv
    #
    wceq
    #
    wa
    #
    vf
    wex
    #
    vm
    cn
    wrex
    #
    wo
    #
    vx
    cio
    #
    cM
    cmul
    cG
    c1
    cseq
    #
    cfv
    #
    vx
    vy
    cA
    cB
    vf
    vk
    vm
    vn
    df-prod
    wph
    @30
    cvv
    wcel
    #
    @28
    @30
    wceq
    cM
    @29
    fvex
    #
    wph
    @27
    vx
    @30
    cvv
    wph
    @27
    @11
    @30
    wceq
    #
    wb
    @31
    wph
    @27
    @33
    wph
    @27
    vx
    wmo
    #
    @2
    @9
    @10
    @30
    cli
    wbr
    #
    w3a
    #
    vm
    cz
    wrex
    #
    @17
    @30
    @22
    wceq
    #
    wa
    #
    vf
    wex
    #
    vm
    cn
    wrex
    #
    wo
    #
    @27
    @33
    wi
    wph
    vx
    vy
    cA
    vk
    vj
    cv
    #
    cB
    csb
    #
    vf
    vi
    vj
    vm
    vn
    @7
    @20
    vk
    vj
    cz
    @6
    @43
    cA
    wcel
    #
    @44
    c1
    cif
    vj
    @6
    nfcv
    @45
    vk
    @44
    c1
    @45
    vk
    nfv
    vk
    @43
    cB
    nfcsb1v
    #
    vk
    c1
    nfcv
    nfif
    vk
    vj
    weq
    #
    @5
    @45
    cB
    @44
    c1
    @4
    @43
    cA
    eleq1
    vk
    @43
    cB
    csbeq1a
    #
    ifbieq1d
    cbvmpt
    wph
    cB
    cc
    wcel
    #
    vk
    cA
    wral
    @45
    @44
    cc
    wcel
    #
    wph
    @49
    vk
    cA
    fprod.4
    ralrimiva
    @49
    @50
    vk
    @43
    cA
    vk
    @44
    cc
    @46
    nfel1
    @47
    cB
    @44
    cc
    @48
    eleq1d
    rspc
    mpan9
    vn
    vi
    cn
    @19
    vj
    vi
    cv
    #
    @16
    cfv
    #
    @44
    csb
    #
    vn
    vi
    weq
    #
    @19
    vk
    @52
    cB
    csb
    @53
    @54
    vk
    @18
    @52
    cB
    @8
    @51
    @16
    fveq2
    csbeq1d
    vk
    vj
    @52
    cB
    csbco
    syl6eqr
    cbvmptv
    prodmo
    wph
    @41
    @37
    wph
    cM
    cn
    wcel
    c1
    cM
    cfz
    co
    #
    cA
    @16
    wf1o
    #
    @30
    cM
    @21
    cfv
    #
    wceq
    #
    wa
    #
    vf
    wex
    #
    @41
    fprod.2
    wph
    cF
    cvv
    wcel
    #
    @55
    cA
    cF
    wf1o
    #
    @30
    cM
    cmul
    vn
    cn
    cC
    cmpt
    #
    c1
    cseq
    #
    cfv
    #
    wceq
    #
    wa
    #
    @60
    wph
    @55
    cA
    cF
    wf
    #
    @55
    cvv
    wcel
    @61
    wph
    @62
    @68
    fprod.3
    @55
    cA
    cF
    f1of
    syl
    c1
    cM
    cfz
    ovex
    @55
    cA
    cvv
    cF
    fex
    sylancl
    wph
    @62
    @66
    fprod.3
    wph
    cmul
    vk
    cG
    @63
    c1
    cM
    wph
    cM
    cn
    c1
    cuz
    cfv
    fprod.2
    nnuz
    syl6eleq
    wph
    @8
    cG
    cfv
    #
    @8
    @63
    cfv
    #
    wceq
    #
    vn
    @55
    wral
    @4
    @55
    wcel
    @4
    cG
    cfv
    #
    @4
    @63
    cfv
    #
    wceq
    #
    wph
    @71
    vn
    @55
    wph
    @8
    @55
    wcel
    #
    wa
    #
    @69
    cC
    @70
    fprod.5
    @76
    @8
    cn
    wcel
    #
    cC
    cvv
    wcel
    @70
    cC
    wceq
    @75
    @77
    wph
    @8
    cM
    elfznn
    adantl
    @76
    cC
    @69
    cvv
    fprod.5
    @8
    cG
    fvex
    syl6eqelr
    vn
    cn
    cC
    cvv
    @63
    @63
    eqid
    fvmpt2
    syl2anc
    eqtr4d
    ralrimiva
    @71
    @74
    vn
    @4
    @55
    vn
    @72
    @73
    vn
    cn
    cC
    @4
    nffvmpt1
    nfeq2
    vn
    vk
    weq
    @69
    @72
    @70
    @73
    @8
    @4
    cG
    fveq2
    @8
    @4
    @63
    fveq2
    eqeq12d
    rspc
    mpan9
    seqfveq
    jca
    @59
    @67
    vf
    cF
    cvv
    @16
    cF
    wceq
    #
    @56
    @62
    @58
    @66
    @55
    cA
    @16
    cF
    f1oeq1
    @78
    @57
    @65
    @30
    @78
    cM
    @21
    @64
    @78
    @20
    @63
    cmul
    c1
    @78
    vn
    cn
    @19
    cC
    @78
    @19
    vk
    @8
    cF
    cfv
    #
    cB
    csb
    cC
    @78
    vk
    @18
    @79
    cB
    @8
    @16
    cF
    fveq1
    csbeq1d
    vk
    @79
    cB
    cC
    @8
    cF
    fvex
    fprod.1
    csbie
    syl6eq
    mpteq2dv
    seqeq3d
    fveq1d
    eqeq2d
    anbi12d
    spcegv
    sylc
    @40
    @60
    vm
    cM
    cn
    @0
    cM
    wceq
    #
    @39
    @59
    vf
    @80
    @17
    @56
    @38
    @58
    @80
    @15
    @55
    wceq
    @17
    @56
    wb
    @0
    cM
    c1
    cfz
    oveq2
    @15
    @55
    cA
    @16
    f1oeq2
    syl
    @80
    @22
    @57
    @30
    @0
    cM
    @21
    fveq2
    eqeq2d
    anbi12d
    exbidv
    rspcev
    syl2anc
    olcd
    #
    @34
    @42
    @27
    @33
    @34
    @27
    @42
    @33
    @31
    @34
    @27
    @42
    wa
    @33
    @32
    @27
    @42
    vx
    @30
    cvv
    @33
    @14
    @37
    @26
    @41
    @33
    @13
    @36
    vm
    cz
    @33
    @12
    @35
    @2
    @9
    @11
    @30
    @10
    cli
    breq2
    3anbi3d
    rexbidv
    @33
    @25
    @40
    vm
    cn
    @33
    @24
    @39
    vf
    @33
    @23
    @38
    @17
    @11
    @30
    @22
    eqeq1
    anbi2d
    exbidv
    rexbidv
    orbi12d
    #
    moi2
    mpanl1
    ancom2s
    expr
    syl2anc
    wph
    @27
    @33
    @42
    @81
    @82
    syl5ibrcom
    impbid
    adantr
    iota5
    mpan2
    syl5eq
end
