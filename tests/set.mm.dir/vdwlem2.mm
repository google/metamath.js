include "cv.mm"
include "cvdwa.mm"
include "cfv.mm"
include "co.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "cn.mm"
include "wrex.mm"
include "wex.mm"
include "cvdwm.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "id.mm"
include "nnaddcl.mm"
include "syl2anr.mm"
include "cmul.mm"
include "wceq.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "simpllr.mm"
include "nncnd.mm"
include "ad3antrrr.mm"
include "cn0.mm"
include "elfznn0.mm"
include "adantl.mm"
include "nn0cnd.mm"
include "simplrl.mm"
include "mulcld.mm"
include "add32d.mm"
include "wral.mm"
include "simplrr.mm"
include "eqid.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "wb.mm"
include "ad2antrr.mm"
include "adantr.mm"
include "vdwapval.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "sseldd.mm"
include "wfn.mm"
include "wf.mm"
include "cuz.mm"
include "elfznn.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "cz.mm"
include "elfzuz3.mm"
include "nnzd.mm"
include "eluzadd.mm"
include "uztrn.mm"
include "syl2anc.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "fmptd.mm"
include "ffn.mm"
include "syl.mm"
include "fniniseg.mm"
include "mpbid.mm"
include "simpld.mm"
include "ralrimiva.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "eqeltrd.mm"
include "fveq2d.mm"
include "fvex.mm"
include "fvmpt.mm"
include "simprd.mm"
include "3eqtr2d.mm"
include "jca.mm"
include "eleq1.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "simprl.mm"
include "3imtr4d.mm"
include "ssrdv.mm"
include "expr.mm"
include "reximdva.mm"
include "sseq1d.mm"
include "rexbidv.mm"
include "syl6an.mm"
include "eximdv.mm"
include "ovex.mm"
include "vdwmc.mm"

theorem vdwlem2
  let wph: wff ph
  let vx: setvar x
  let cR: class R
  let cF: class F
  let cG: class G
  let cK: class K
  let cM: class M
  let cN: class N
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vm: setvar m
  let vn: setvar n
  assume vdwlem2.r: |- ( ph -> R e. Fin )
  assume vdwlem2.k: |- ( ph -> K e. NN0 )
  assume vdwlem2.w: |- ( ph -> W e. NN )
  assume vdwlem2.n: |- ( ph -> N e. NN )
  assume vdwlem2.f: |- ( ph -> F : ( 1 ... M ) --> R )
  assume vdwlem2.m: |- ( ph -> M e. ( ZZ>= ` ( W + N ) ) )
  assume vdwlem2.g: |- G = ( x e. ( 1 ... W ) |-> ( F ` ( x + N ) ) )

  disjoint F x
  disjoint K x
  disjoint M x
  disjoint ph x
  disjoint G x
  disjoint N x
  disjoint R x
  disjoint W x
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a m
  disjoint a x
  disjoint F a
  disjoint b c
  disjoint b d
  disjoint b m
  disjoint b x
  disjoint F b
  disjoint c d
  disjoint c m
  disjoint c x
  disjoint F c
  disjoint d m
  disjoint d x
  disjoint F d
  disjoint m x
  disjoint F m
  disjoint a n
  disjoint K a
  disjoint b n
  disjoint K b
  disjoint c n
  disjoint K c
  disjoint d n
  disjoint K d
  disjoint m n
  disjoint K m
  disjoint n x
  disjoint K n
  disjoint M m
  disjoint a ph
  disjoint c ph
  disjoint d ph
  disjoint m ph
  disjoint G a
  disjoint G c
  disjoint G d
  disjoint G m
  disjoint N b
  disjoint N d
  disjoint N m
  assert |- ( ph -> ( K MonoAP G -> K MonoAP F ) )

  proof
    wph
    va
    cv
    #
    vd
    cv
    #
    cK
    cvdwa
    cfv
    #
    co
    #
    cG
    ccnv
    vc
    cv
    #
    csn
    #
    cima
    #
    wss
    #
    vd
    cn
    wrex
    #
    va
    cn
    wrex
    #
    vc
    wex
    vb
    cv
    #
    @1
    @2
    co
    #
    cF
    ccnv
    @5
    cima
    #
    wss
    #
    vd
    cn
    wrex
    #
    vb
    cn
    wrex
    #
    vc
    wex
    cK
    cG
    cvdwm
    wbr
    cK
    cF
    cvdwm
    wbr
    wph
    @9
    @15
    vc
    wph
    @8
    @15
    va
    cn
    wph
    @0
    cn
    wcel
    #
    wa
    #
    @0
    cN
    caddc
    co
    #
    cn
    wcel
    #
    @8
    @18
    @1
    @2
    co
    #
    @12
    wss
    #
    vd
    cn
    wrex
    #
    @15
    @16
    @16
    cN
    cn
    wcel
    #
    @19
    wph
    @16
    id
    vdwlem2.n
    @0
    cN
    nnaddcl
    syl2anr
    #
    @17
    @7
    @21
    vd
    cn
    @17
    @1
    cn
    wcel
    #
    @7
    @21
    @17
    @25
    @7
    wa
    #
    wa
    #
    vx
    @20
    @12
    @27
    vx
    cv
    #
    @18
    vm
    cv
    #
    @1
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vm
    cc0
    cK
    c1
    cmin
    co
    #
    cfz
    co
    #
    wrex
    #
    @28
    c1
    cM
    cfz
    co
    #
    wcel
    #
    @28
    cF
    cfv
    #
    @4
    wceq
    #
    wa
    #
    @28
    @20
    wcel
    #
    @28
    @12
    wcel
    #
    @27
    @32
    @40
    vm
    @34
    @27
    @29
    @34
    wcel
    #
    wa
    #
    @40
    @32
    @31
    @36
    wcel
    #
    @31
    cF
    cfv
    #
    @4
    wceq
    #
    wa
    @44
    @45
    @47
    @44
    @31
    @0
    @30
    caddc
    co
    #
    cN
    caddc
    co
    #
    @36
    @44
    @0
    cN
    @30
    @44
    @0
    wph
    @16
    @26
    @43
    simpllr
    #
    nncnd
    @44
    cN
    wph
    @23
    @16
    @26
    @43
    vdwlem2.n
    ad3antrrr
    nncnd
    @44
    @29
    @1
    @44
    @29
    @43
    @29
    cn0
    wcel
    @27
    @29
    @33
    elfznn0
    adantl
    nn0cnd
    @44
    @1
    @17
    @25
    @7
    @43
    simplrl
    #
    nncnd
    mulcld
    add32d
    #
    @44
    @48
    c1
    cW
    cfz
    co
    #
    wcel
    #
    @28
    cN
    caddc
    co
    #
    @36
    wcel
    #
    vx
    @53
    wral
    #
    @49
    @36
    wcel
    #
    @44
    @54
    @48
    cG
    cfv
    #
    @4
    wceq
    #
    @44
    @48
    @6
    wcel
    #
    @54
    @60
    wa
    #
    @44
    @3
    @6
    @48
    @17
    @25
    @7
    @43
    simplrr
    @44
    @48
    @3
    wcel
    #
    @48
    @0
    vn
    cv
    #
    @1
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vn
    @34
    wrex
    #
    @43
    @68
    @27
    @43
    @48
    @48
    wceq
    #
    @68
    @48
    eqid
    @67
    @69
    vn
    @29
    @34
    @64
    @29
    wceq
    #
    @66
    @48
    @48
    @70
    @65
    @30
    @0
    caddc
    @64
    @29
    @1
    cmul
    oveq1
    oveq2d
    eqeq2d
    rspcev
    mpan2
    adantl
    @44
    cK
    cn0
    wcel
    #
    @16
    @25
    @63
    @68
    wb
    @27
    @71
    @43
    wph
    @71
    @16
    @26
    vdwlem2.k
    ad2antrr
    #
    adantr
    @50
    @51
    @0
    @1
    vn
    cK
    @48
    vdwapval
    syl3anc
    mpbird
    sseldd
    @44
    cG
    @53
    wfn
    #
    @61
    @62
    wb
    wph
    @73
    @16
    @26
    @43
    wph
    @53
    cR
    cG
    wf
    @73
    wph
    vx
    @53
    @55
    cF
    cfv
    #
    cR
    cG
    wph
    @28
    @53
    wcel
    #
    @56
    @74
    cR
    wcel
    wph
    @75
    wa
    #
    @55
    c1
    cuz
    cfv
    #
    wcel
    cM
    @55
    cuz
    cfv
    #
    wcel
    #
    @56
    @76
    @55
    cn
    @77
    @75
    @28
    cn
    wcel
    @23
    @55
    cn
    wcel
    wph
    @28
    cW
    elfznn
    vdwlem2.n
    @28
    cN
    nnaddcl
    syl2anr
    nnuz
    syl6eleq
    @76
    cM
    cW
    cN
    caddc
    co
    #
    cuz
    cfv
    wcel
    #
    @80
    @78
    wcel
    #
    @79
    wph
    @81
    @75
    vdwlem2.m
    adantr
    @75
    cW
    @28
    cuz
    cfv
    wcel
    cN
    cz
    wcel
    @82
    wph
    @28
    c1
    cW
    elfzuz3
    wph
    cN
    vdwlem2.n
    nnzd
    cN
    @28
    cW
    eluzadd
    syl2anr
    @80
    cM
    @55
    uztrn
    syl2anc
    @55
    c1
    cM
    elfzuzb
    sylanbrc
    #
    wph
    @36
    cR
    @55
    cF
    vdwlem2.f
    ffvelrnda
    syldan
    vdwlem2.g
    fmptd
    #
    @53
    cR
    cG
    ffn
    syl
    ad3antrrr
    @53
    @4
    @48
    cG
    fniniseg
    syl
    mpbid
    #
    simpld
    #
    wph
    @57
    @16
    @26
    @43
    wph
    @56
    vx
    @53
    @83
    ralrimiva
    ad3antrrr
    @56
    @58
    vx
    @48
    @53
    @28
    @48
    wceq
    #
    @55
    @49
    @36
    @28
    @48
    cN
    caddc
    oveq1
    #
    eleq1d
    rspcv
    sylc
    eqeltrd
    @44
    @46
    @49
    cF
    cfv
    #
    @59
    @4
    @44
    @31
    @49
    cF
    @52
    fveq2d
    @44
    @54
    @59
    @89
    wceq
    @86
    vx
    @48
    @74
    @89
    @53
    cG
    @87
    @55
    @49
    cF
    @88
    fveq2d
    vdwlem2.g
    @49
    cF
    fvex
    fvmpt
    syl
    @44
    @54
    @60
    @85
    simprd
    3eqtr2d
    jca
    @32
    @37
    @45
    @39
    @47
    @28
    @31
    @36
    eleq1
    @32
    @38
    @46
    @4
    @28
    @31
    cF
    fveq2
    eqeq1d
    anbi12d
    syl5ibrcom
    rexlimdva
    @27
    @71
    @19
    @25
    @41
    @35
    wb
    @72
    @17
    @19
    @26
    @24
    adantr
    @17
    @25
    @7
    simprl
    @18
    @1
    vm
    cK
    @28
    vdwapval
    syl3anc
    @27
    cF
    @36
    wfn
    #
    @42
    @40
    wb
    wph
    @90
    @16
    @26
    wph
    @36
    cR
    cF
    wf
    @90
    vdwlem2.f
    @36
    cR
    cF
    ffn
    syl
    ad2antrr
    @36
    @4
    @28
    cF
    fniniseg
    syl
    3imtr4d
    ssrdv
    expr
    reximdva
    @14
    @22
    vb
    @18
    cn
    @10
    @18
    wceq
    #
    @13
    @21
    vd
    cn
    @91
    @11
    @20
    @12
    @10
    @18
    @1
    @2
    oveq1
    sseq1d
    rexbidv
    rspcev
    syl6an
    rexlimdva
    eximdv
    wph
    cR
    cG
    cK
    @53
    va
    vc
    vd
    c1
    cW
    cfz
    ovex
    vdwlem2.k
    @84
    vdwmc
    wph
    cR
    cF
    cK
    @36
    vb
    vc
    vd
    c1
    cM
    cfz
    ovex
    vdwlem2.k
    vdwlem2.f
    vdwmc
    3imtr4d
end
