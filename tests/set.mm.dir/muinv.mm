include "cn.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "cmu.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "csu.mm"
include "cc.mm"
include "feqmptd.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "ad2antrr.mm"
include "fveq1d.mm"
include "cz.mm"
include "cc0.mm"
include "clt.mm"
include "breq1.mm"
include "elrab.mm"
include "simprbi.mm"
include "adantl.mm"
include "wne.mm"
include "wb.mm"
include "elrabi.mm"
include "nnzd.mm"
include "nnne0d.mm"
include "nnz.mm"
include "ad2antlr.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "cr.mm"
include "nnre.mm"
include "nngt0.mm"
include "jca.mm"
include "syl.mm"
include "divgt0.mm"
include "syl2anc.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "breq2.mm"
include "rabbidv.mm"
include "sumeq1d.mm"
include "eqid.mm"
include "sumex.mm"
include "fvmpt.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "c1.mm"
include "cfz.mm"
include "cfn.mm"
include "wss.mm"
include "fzfid.mm"
include "dvdsssfz1.mm"
include "ssfi.mm"
include "mucl.mm"
include "zcnd.mm"
include "wf.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "fsummulc2.mm"
include "sumeq2dv.mm"
include "simpr.mm"
include "adantrr.mm"
include "anasss.mm"
include "mulcld.mm"
include "fsumdvdsdiag.mm"
include "cif.mm"
include "csn.mm"
include "ssrab2.mm"
include "dvdsdivcl.mm"
include "adantll.mm"
include "sseldi.mm"
include "musum.mm"
include "oveq1d.mm"
include "adantr.mm"
include "fsummulc1.mm"
include "ovif.mm"
include "nncn.mm"
include "nncnd.mm"
include "1cnd.mm"
include "divmuld.mm"
include "mulid1d.mm"
include "eqeq1d.mm"
include "bitrd.mm"
include "mulid2d.mm"
include "mul02d.mm"
include "ifbieq12d.mm"
include "syl5eq.mm"
include "3eqtr3d.mm"
include "iddvds.mm"
include "snssd.mm"
include "sselda.mm"
include "syldan.mm"
include "0cn.mm"
include "ifcl.mm"
include "sylancl.mm"
include "cdif.mm"
include "eldifsni.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "fsumss.mm"
include "ffvelrnda.mm"
include "iftrue.mm"
include "fveq2.mm"
include "sumsn.mm"
include "3eqtr2d.mm"
include "3eqtrd.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"

theorem muinv
  let wph: wff ph
  let vx: setvar x
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cA: class A
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vz: setvar z
  let cN: class N
  let cB: class B
  let cC: class C
  assume muinv.1: |- ( ph -> F : NN --> CC )
  assume muinv.2: |- ( ph -> G = ( n e. NN |-> sum_ k e. { x e. NN | x || n } ( F ` k ) ) )

  disjoint k m
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint F j
  disjoint k n
  disjoint F k
  disjoint m n
  disjoint F m
  disjoint F n
  disjoint j x
  disjoint k x
  disjoint m x
  disjoint n x
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint A k
  disjoint A m
  disjoint j p
  disjoint j q
  disjoint j s
  disjoint j z
  disjoint N j
  disjoint k p
  disjoint k q
  disjoint k s
  disjoint k z
  disjoint N k
  disjoint m p
  disjoint m q
  disjoint m s
  disjoint m z
  disjoint N m
  disjoint n p
  disjoint n q
  disjoint n s
  disjoint n z
  disjoint N n
  disjoint p q
  disjoint p s
  disjoint p x
  disjoint p z
  disjoint N p
  disjoint q s
  disjoint q x
  disjoint q z
  disjoint N q
  disjoint s x
  disjoint s z
  disjoint N s
  disjoint x z
  disjoint N x
  disjoint N z
  disjoint B k
  disjoint C m
  assert |- ( ph -> F = ( m e. NN |-> sum_ j e. { x e. NN | x || m } ( ( mmu ` j ) x. ( G ` ( m / j ) ) ) ) )

  proof
    wph
    cF
    vm
    cn
    vm
    cv
    #
    cF
    cfv
    #
    cmpt
    vm
    cn
    vx
    cv
    #
    @0
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    vj
    cv
    #
    cmu
    cfv
    #
    @0
    @5
    cdiv
    co
    #
    cG
    cfv
    #
    cmul
    co
    #
    vj
    csu
    #
    cmpt
    wph
    vm
    cn
    cc
    cF
    muinv.1
    feqmptd
    wph
    vm
    cn
    @10
    @1
    wph
    @0
    cn
    wcel
    #
    wa
    #
    @10
    @4
    @2
    @7
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    @6
    vk
    cv
    #
    cF
    cfv
    #
    cmul
    co
    #
    vk
    csu
    #
    vj
    csu
    @4
    @2
    @0
    @15
    cdiv
    co
    #
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    @17
    vj
    csu
    #
    vk
    csu
    #
    @1
    @12
    @4
    @9
    @18
    vj
    @12
    @5
    @4
    wcel
    #
    wa
    #
    @9
    @6
    @14
    @16
    vk
    csu
    #
    cmul
    co
    @18
    @25
    @8
    @26
    @6
    cmul
    @25
    @8
    @7
    vn
    cn
    @2
    vn
    cv
    #
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    @16
    vk
    csu
    #
    cmpt
    #
    cfv
    #
    @26
    @25
    @7
    cG
    @31
    wph
    cG
    @31
    wceq
    @11
    @24
    muinv.2
    ad2antrr
    fveq1d
    @25
    @7
    cn
    wcel
    #
    @32
    @26
    wceq
    @25
    @7
    cz
    wcel
    #
    cc0
    @7
    clt
    wbr
    #
    @33
    @25
    @5
    @0
    cdvds
    wbr
    #
    @34
    @24
    @36
    @12
    @24
    @5
    cn
    wcel
    #
    @36
    @3
    @36
    vx
    @5
    cn
    @2
    @5
    @0
    cdvds
    breq1
    elrab
    simprbi
    adantl
    @25
    @5
    cz
    wcel
    @5
    cc0
    wne
    @0
    cz
    wcel
    #
    @36
    @34
    wb
    @25
    @5
    @24
    @37
    @12
    @3
    vx
    @5
    cn
    elrabi
    adantl
    #
    nnzd
    @25
    @5
    @39
    nnne0d
    @11
    @38
    wph
    @24
    @0
    nnz
    ad2antlr
    @5
    @0
    dvdsval2
    syl3anc
    mpbid
    @25
    @0
    cr
    wcel
    #
    cc0
    @0
    clt
    wbr
    #
    wa
    #
    @5
    cr
    wcel
    #
    cc0
    @5
    clt
    wbr
    #
    wa
    #
    @35
    @11
    @42
    wph
    @24
    @11
    @40
    @41
    @0
    nnre
    @0
    nngt0
    jca
    ad2antlr
    @25
    @37
    @45
    @39
    @37
    @43
    @44
    @5
    nnre
    @5
    nngt0
    jca
    syl
    @0
    @5
    divgt0
    syl2anc
    @7
    elnnz
    sylanbrc
    #
    vn
    @7
    @30
    @26
    cn
    @31
    @27
    @7
    wceq
    #
    @29
    @14
    @16
    vk
    @47
    @28
    @13
    vx
    cn
    @27
    @7
    @2
    cdvds
    breq2
    rabbidv
    sumeq1d
    @31
    eqid
    @14
    @16
    vk
    sumex
    fvmpt
    syl
    eqtrd
    oveq2d
    @25
    @14
    @16
    @6
    vk
    @25
    c1
    @7
    cfz
    co
    #
    cfn
    wcel
    @14
    @48
    wss
    #
    @14
    cfn
    wcel
    @25
    c1
    @7
    fzfid
    @25
    @33
    @49
    @46
    @7
    vx
    dvdsssfz1
    syl
    @48
    @14
    ssfi
    syl2anc
    @25
    @6
    @25
    @37
    @6
    cz
    wcel
    #
    @39
    @5
    mucl
    #
    syl
    zcnd
    #
    @25
    cn
    cc
    cF
    wf
    #
    @15
    cn
    wcel
    #
    @16
    cc
    wcel
    #
    @15
    @14
    wcel
    #
    wph
    @53
    @11
    @24
    muinv.1
    ad2antrr
    @13
    vx
    @15
    cn
    elrabi
    cn
    cc
    @15
    cF
    ffvelrn
    #
    syl2an
    #
    fsummulc2
    eqtrd
    sumeq2dv
    @12
    vx
    @17
    vj
    vk
    @0
    wph
    @11
    simpr
    #
    @12
    @24
    @56
    wa
    wa
    @6
    @16
    @12
    @24
    @6
    cc
    wcel
    @56
    @52
    adantrr
    @12
    @24
    @56
    @55
    @58
    anasss
    mulcld
    fsumdvdsdiag
    @12
    @23
    @4
    @15
    @0
    wceq
    #
    @16
    cc0
    cif
    #
    vk
    csu
    @0
    csn
    #
    @61
    vk
    csu
    #
    @1
    @12
    @4
    @22
    @61
    vk
    @12
    @15
    @4
    wcel
    #
    wa
    #
    @21
    @6
    vj
    csu
    #
    @16
    cmul
    co
    @19
    c1
    wceq
    #
    c1
    cc0
    cif
    #
    @16
    cmul
    co
    #
    @22
    @61
    @65
    @66
    @68
    @16
    cmul
    @65
    @19
    cn
    wcel
    #
    @66
    @68
    wceq
    @65
    @4
    cn
    @19
    @3
    vx
    cn
    ssrab2
    @11
    @64
    @19
    @4
    wcel
    wph
    vx
    @15
    @0
    dvdsdivcl
    adantll
    sseldi
    #
    vj
    vx
    @19
    musum
    syl
    oveq1d
    @65
    @21
    @6
    @16
    vj
    @65
    c1
    @19
    cfz
    co
    #
    cfn
    wcel
    @21
    @72
    wss
    #
    @21
    cfn
    wcel
    @65
    c1
    @19
    fzfid
    @65
    @70
    @73
    @71
    @19
    vx
    dvdsssfz1
    syl
    @72
    @21
    ssfi
    syl2anc
    @12
    @53
    @54
    @55
    @64
    wph
    @53
    @11
    muinv.1
    adantr
    @3
    vx
    @15
    cn
    elrabi
    #
    @57
    syl2an
    #
    @65
    @5
    @21
    wcel
    #
    wa
    #
    @6
    @77
    @37
    @50
    @77
    @21
    cn
    @5
    @20
    vx
    cn
    ssrab2
    @65
    @76
    simpr
    sseldi
    @51
    syl
    zcnd
    fsummulc1
    @65
    @69
    @67
    c1
    @16
    cmul
    co
    #
    cc0
    @16
    cmul
    co
    #
    cif
    @61
    @67
    c1
    cc0
    @16
    cmul
    ovif
    @65
    @67
    @60
    @78
    @79
    @16
    cc0
    @65
    @67
    @15
    c1
    cmul
    co
    #
    @0
    wceq
    @60
    @65
    @0
    @15
    c1
    @11
    @0
    cc
    wcel
    wph
    @64
    @0
    nncn
    ad2antlr
    @65
    @15
    @64
    @54
    @12
    @74
    adantl
    #
    nncnd
    #
    @65
    1cnd
    @65
    @15
    @81
    nnne0d
    divmuld
    @65
    @80
    @15
    @0
    @65
    @15
    @82
    mulid1d
    eqeq1d
    bitrd
    @65
    @16
    @75
    mulid2d
    @65
    @16
    @75
    mul02d
    ifbieq12d
    syl5eq
    3eqtr3d
    sumeq2dv
    @12
    @62
    @4
    @61
    vk
    @12
    @0
    @4
    @12
    @11
    @0
    @0
    cdvds
    wbr
    #
    @0
    @4
    wcel
    @59
    @12
    @38
    @83
    @12
    @0
    @59
    nnzd
    @0
    iddvds
    syl
    @3
    @83
    vx
    @0
    cn
    @2
    @0
    @0
    cdvds
    breq1
    elrab
    sylanbrc
    snssd
    #
    @12
    @15
    @62
    wcel
    #
    wa
    @55
    cc0
    cc
    wcel
    @61
    cc
    wcel
    @12
    @85
    @64
    @55
    @12
    @62
    @4
    @15
    @84
    sselda
    @75
    syldan
    0cn
    @60
    @16
    cc0
    cc
    ifcl
    sylancl
    @12
    @15
    @4
    @62
    cdif
    wcel
    #
    wa
    #
    @60
    @16
    cc0
    @87
    @15
    @0
    @86
    @15
    @0
    wne
    @12
    @15
    @4
    @0
    eldifsni
    adantl
    neneqd
    iffalsed
    @12
    c1
    @0
    cfz
    co
    #
    cfn
    wcel
    @4
    @88
    wss
    #
    @4
    cfn
    wcel
    @12
    c1
    @0
    fzfid
    @11
    @89
    wph
    @0
    vx
    dvdsssfz1
    adantl
    @88
    @4
    ssfi
    syl2anc
    fsumss
    @12
    @11
    @1
    cc
    wcel
    @63
    @1
    wceq
    @59
    wph
    cn
    cc
    @0
    cF
    muinv.1
    ffvelrnda
    @61
    @1
    vk
    @0
    cn
    @60
    @61
    @16
    @1
    @60
    @16
    cc0
    iftrue
    @15
    @0
    cF
    fveq2
    eqtrd
    sumsn
    syl2anc
    3eqtr2d
    3eqtrd
    mpteq2dva
    eqtr4d
end
