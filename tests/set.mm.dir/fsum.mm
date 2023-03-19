include "csu.mm"
include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "caddc.mm"
include "cz.mm"
include "wcel.mm"
include "csb.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wf1o.mm"
include "cn.mm"
include "wceq.mm"
include "wex.mm"
include "wo.mm"
include "cio.mm"
include "df-sum.mm"
include "cvv.mm"
include "fvex.mm"
include "wb.mm"
include "wmo.mm"
include "wi.mm"
include "eleq1.mm"
include "csbeq1.mm"
include "ifbieq1d.mm"
include "cbvmptv.mm"
include "cc.mm"
include "wral.mm"
include "ralrimiva.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "rspc.mm"
include "mpan9.mm"
include "fveq2.mm"
include "csbeq1d.mm"
include "csbco.mm"
include "syl6eqr.mm"
include "summo.mm"
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
include "anbi2d.mm"
include "rexbidv.mm"
include "eqeq1.mm"
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

theorem fsum
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
  assume fsum.1: |- ( k = ( F ` n ) -> B = C )
  assume fsum.2: |- ( ph -> M e. NN )
  assume fsum.3: |- ( ph -> F : ( 1 ... M ) -1-1-onto-> A )
  assume fsum.4: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume fsum.5: |- ( ( ph /\ n e. ( 1 ... M ) ) -> ( G ` n ) = C )

  disjoint B n
  disjoint C k
  disjoint k n
  disjoint F k
  disjoint F n
  disjoint k ph
  disjoint n ph
  disjoint A k
  disjoint A n
  disjoint G k
  disjoint G n
  disjoint M k
  disjoint M n
  disjoint f i
  disjoint f j
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint B f
  disjoint i j
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint B i
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint B j
  disjoint m n
  disjoint m x
  disjoint B m
  disjoint n x
  disjoint B x
  disjoint f k
  disjoint C f
  disjoint k m
  disjoint k x
  disjoint C m
  disjoint C x
  disjoint F f
  disjoint f ph
  disjoint i k
  disjoint i ph
  disjoint j k
  disjoint j ph
  disjoint m ph
  disjoint ph x
  disjoint A f
  disjoint A i
  disjoint A j
  disjoint A m
  disjoint A x
  disjoint G f
  disjoint G m
  disjoint G x
  disjoint M f
  disjoint M m
  disjoint M x
  assert |- ( ph -> sum_ k e. A B = ( seq 1 ( + , G ) ` M ) )

  proof
    wph
    cA
    cB
    vk
    csu
    cA
    vm
    cv
    #
    cuz
    cfv
    wss
    #
    caddc
    vn
    cz
    vn
    cv
    #
    cA
    wcel
    #
    vk
    @2
    cB
    csb
    #
    cc0
    cif
    #
    cmpt
    #
    @0
    cseq
    #
    vx
    cv
    #
    cli
    wbr
    #
    wa
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
    @8
    @0
    caddc
    vn
    cn
    vk
    @2
    @13
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
    caddc
    cG
    c1
    cseq
    #
    cfv
    #
    vx
    cA
    cB
    vf
    vk
    vm
    vn
    df-sum
    wph
    @27
    cvv
    wcel
    #
    @25
    @27
    wceq
    cM
    @26
    fvex
    #
    wph
    @24
    vx
    @27
    cvv
    wph
    @24
    @8
    @27
    wceq
    #
    wb
    @28
    wph
    @24
    @30
    wph
    @24
    vx
    wmo
    #
    @1
    @7
    @27
    cli
    wbr
    #
    wa
    #
    vm
    cz
    wrex
    #
    @14
    @27
    @19
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
    @24
    @30
    wi
    wph
    vx
    cA
    vk
    vj
    cv
    #
    cB
    csb
    #
    vf
    vj
    vm
    vi
    @6
    @17
    vn
    vj
    cz
    @5
    @40
    cA
    wcel
    #
    @41
    cc0
    cif
    @2
    @40
    wceq
    @3
    @42
    @4
    @41
    cc0
    @2
    @40
    cA
    eleq1
    vk
    @2
    @40
    cB
    csbeq1
    ifbieq1d
    cbvmptv
    wph
    cB
    cc
    wcel
    #
    vk
    cA
    wral
    @42
    @41
    cc
    wcel
    #
    wph
    @43
    vk
    cA
    fsum.4
    ralrimiva
    @43
    @44
    vk
    @40
    cA
    vk
    @41
    cc
    vk
    @40
    cB
    nfcsb1v
    nfel1
    vk
    cv
    #
    @40
    wceq
    cB
    @41
    cc
    vk
    @40
    cB
    csbeq1a
    eleq1d
    rspc
    mpan9
    vn
    vi
    cn
    @16
    vj
    vi
    cv
    #
    @13
    cfv
    #
    @41
    csb
    #
    @2
    @46
    wceq
    #
    @16
    vk
    @47
    cB
    csb
    @48
    @49
    vk
    @15
    @47
    cB
    @2
    @46
    @13
    fveq2
    csbeq1d
    vk
    vj
    @47
    cB
    csbco
    syl6eqr
    cbvmptv
    summo
    wph
    @38
    @34
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
    @13
    wf1o
    #
    @27
    cM
    @18
    cfv
    #
    wceq
    #
    wa
    #
    vf
    wex
    #
    @38
    fsum.2
    wph
    cF
    cvv
    wcel
    #
    @50
    cA
    cF
    wf1o
    #
    @27
    cM
    caddc
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
    @55
    wph
    @50
    cA
    cF
    wf
    #
    @50
    cvv
    wcel
    @56
    wph
    @57
    @63
    fsum.3
    @50
    cA
    cF
    f1of
    syl
    c1
    cM
    cfz
    ovex
    @50
    cA
    cvv
    cF
    fex
    sylancl
    wph
    @57
    @61
    fsum.3
    wph
    caddc
    vk
    cG
    @58
    c1
    cM
    wph
    cM
    cn
    c1
    cuz
    cfv
    fsum.2
    nnuz
    syl6eleq
    wph
    @2
    cG
    cfv
    #
    @2
    @58
    cfv
    #
    wceq
    #
    vn
    @50
    wral
    @45
    @50
    wcel
    @45
    cG
    cfv
    #
    @45
    @58
    cfv
    #
    wceq
    #
    wph
    @66
    vn
    @50
    wph
    @2
    @50
    wcel
    #
    wa
    #
    @64
    cC
    @65
    fsum.5
    @71
    @2
    cn
    wcel
    #
    cC
    cvv
    wcel
    @65
    cC
    wceq
    @70
    @72
    wph
    @2
    cM
    elfznn
    adantl
    @71
    cC
    @64
    cvv
    fsum.5
    @2
    cG
    fvex
    syl6eqelr
    vn
    cn
    cC
    cvv
    @58
    @58
    eqid
    fvmpt2
    syl2anc
    eqtr4d
    ralrimiva
    @66
    @69
    vn
    @45
    @50
    vn
    @67
    @68
    vn
    cn
    cC
    @45
    nffvmpt1
    nfeq2
    @2
    @45
    wceq
    @64
    @67
    @65
    @68
    @2
    @45
    cG
    fveq2
    @2
    @45
    @58
    fveq2
    eqeq12d
    rspc
    mpan9
    seqfveq
    jca
    @54
    @62
    vf
    cF
    cvv
    @13
    cF
    wceq
    #
    @51
    @57
    @53
    @61
    @50
    cA
    @13
    cF
    f1oeq1
    @73
    @52
    @60
    @27
    @73
    cM
    @18
    @59
    @73
    @17
    @58
    caddc
    c1
    @73
    vn
    cn
    @16
    cC
    @73
    @16
    vk
    @2
    cF
    cfv
    #
    cB
    csb
    cC
    @73
    vk
    @15
    @74
    cB
    @2
    @13
    cF
    fveq1
    csbeq1d
    vk
    @74
    cB
    cC
    @2
    cF
    fvex
    fsum.1
    csbie
    syl6eq
    mpteq2dv
    seqeq3d
    fveq1d
    eqeq2d
    anbi12d
    spcegv
    sylc
    @37
    @55
    vm
    cM
    cn
    @0
    cM
    wceq
    #
    @36
    @54
    vf
    @75
    @14
    @51
    @35
    @53
    @75
    @12
    @50
    wceq
    @14
    @51
    wb
    @0
    cM
    c1
    cfz
    oveq2
    @12
    @50
    cA
    @13
    f1oeq2
    syl
    @75
    @19
    @52
    @27
    @0
    cM
    @18
    fveq2
    eqeq2d
    anbi12d
    exbidv
    rspcev
    syl2anc
    olcd
    #
    @31
    @39
    @24
    @30
    @31
    @24
    @39
    @30
    @28
    @31
    @24
    @39
    wa
    @30
    @29
    @24
    @39
    vx
    @27
    cvv
    @30
    @11
    @34
    @23
    @38
    @30
    @10
    @33
    vm
    cz
    @30
    @9
    @32
    @1
    @8
    @27
    @7
    cli
    breq2
    anbi2d
    rexbidv
    @30
    @22
    @37
    vm
    cn
    @30
    @21
    @36
    vf
    @30
    @20
    @35
    @14
    @8
    @27
    @19
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
    @24
    @30
    @39
    @76
    @77
    syl5ibrcom
    impbid
    adantr
    iota5
    mpan2
    syl5eq
end
