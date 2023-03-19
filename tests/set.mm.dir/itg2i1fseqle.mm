include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "cv.mm"
include "cr.mm"
include "wral.mm"
include "cmpt.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "ad2antlr.mm"
include "c1.mm"
include "nnuz.mm"
include "simplr.mm"
include "cli.mm"
include "mpteq2dv.mm"
include "breq12d.mm"
include "rspccva.mm"
include "sylan.mm"
include "adantlr.mm"
include "adantl.mm"
include "citg1.mm"
include "cdm.mm"
include "wf.mm"
include "ffvelrnda.mm"
include "i1ff.mm"
include "syl.mm"
include "an32s.mm"
include "eqeltrd.mm"
include "adantllr.mm"
include "caddc.mm"
include "co.mm"
include "c0p.mm"
include "simpr.mm"
include "ralimi.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wfn.mm"
include "ffn.mm"
include "3syl.mm"
include "peano2nn.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "reex.mm"
include "a1i.mm"
include "inidm.mm"
include "eqidd.mm"
include "ofrfval.mm"
include "mpbid.mm"
include "r19.21bi.mm"
include "3brtr4d.mm"
include "climub.mm"
include "eqbrtrrd.mm"
include "ralrimiva.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "cico.mm"
include "wss.mm"
include "icossicc.mm"
include "fss.mm"
include "sylancl.mm"
include "adantr.mm"
include "mpbird.mm"

theorem itg2i1fseqle
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let vn: setvar n
  let cF: class F
  let cM: class M
  let vk: setvar k
  let vm: setvar m
  let vy: setvar y
  let vz: setvar z
  let cS: class S
  assume itg2i1fseq.1: |- ( ph -> F e. MblFn )
  assume itg2i1fseq.2: |- ( ph -> F : RR --> ( 0 [,) +oo ) )
  assume itg2i1fseq.3: |- ( ph -> P : NN --> dom S.1 )
  assume itg2i1fseq.4: |- ( ph -> A. n e. NN ( 0p oR <_ ( P ` n ) /\ ( P ` n ) oR <_ ( P ` ( n + 1 ) ) ) )
  assume itg2i1fseq.5: |- ( ph -> A. x e. RR ( n e. NN |-> ( ( P ` n ) ` x ) ) ~~> ( F ` x ) )

  disjoint n x
  disjoint F n
  disjoint F x
  disjoint M n
  disjoint P n
  disjoint P x
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint M k
  disjoint M y
  disjoint M z
  disjoint P k
  disjoint P m
  disjoint P y
  disjoint P z
  disjoint k ph
  disjoint m ph
  disjoint ph y
  disjoint ph z
  disjoint S k
  disjoint S y
  disjoint S z
  assert |- ( ( ph /\ M e. NN ) -> ( P ` M ) oR <_ F )

  proof
    wph
    cM
    cn
    wcel
    #
    wa
    #
    cM
    cP
    cfv
    #
    cF
    cle
    cofr
    #
    wbr
    vy
    cv
    #
    @2
    cfv
    #
    @4
    cF
    cfv
    #
    cle
    wbr
    #
    vy
    cr
    wral
    @1
    @7
    vy
    cr
    @1
    @4
    cr
    wcel
    #
    wa
    #
    cM
    vn
    cn
    @4
    vn
    cv
    #
    cP
    cfv
    #
    cfv
    #
    cmpt
    #
    cfv
    #
    @5
    @6
    cle
    @0
    @14
    @5
    wceq
    wph
    @8
    vn
    cM
    @12
    @5
    cn
    @13
    @10
    cM
    wceq
    @4
    @11
    @2
    @10
    cM
    cP
    fveq2
    fveq1d
    @13
    eqid
    #
    @4
    @2
    fvex
    fvmpt
    ad2antlr
    @9
    @6
    vk
    @13
    c1
    cM
    cn
    nnuz
    wph
    @0
    @8
    simplr
    wph
    @8
    @13
    @6
    cli
    wbr
    #
    @0
    wph
    vn
    cn
    vx
    cv
    #
    @11
    cfv
    #
    cmpt
    #
    @17
    cF
    cfv
    #
    cli
    wbr
    #
    vx
    cr
    wral
    @8
    @16
    itg2i1fseq.5
    @21
    @16
    vx
    @4
    cr
    @17
    @4
    wceq
    #
    @19
    @13
    @20
    @6
    cli
    @22
    vn
    cn
    @18
    @12
    @17
    @4
    @11
    fveq2
    mpteq2dv
    @17
    @4
    cF
    fveq2
    breq12d
    rspccva
    sylan
    adantlr
    wph
    @8
    vk
    cv
    #
    cn
    wcel
    #
    @23
    @13
    cfv
    #
    cr
    wcel
    @0
    wph
    @8
    wa
    #
    @24
    wa
    #
    @25
    @4
    @23
    cP
    cfv
    #
    cfv
    #
    cr
    @24
    @25
    @29
    wceq
    @26
    vn
    @23
    @12
    @29
    cn
    @13
    @10
    @23
    wceq
    #
    @4
    @11
    @28
    @10
    @23
    cP
    fveq2
    #
    fveq1d
    @15
    @4
    @28
    fvex
    fvmpt
    adantl
    #
    wph
    @24
    @8
    @29
    cr
    wcel
    wph
    @24
    wa
    #
    cr
    cr
    @4
    @28
    @33
    @28
    citg1
    cdm
    #
    wcel
    #
    cr
    cr
    @28
    wf
    #
    wph
    cn
    @34
    @23
    cP
    itg2i1fseq.3
    ffvelrnda
    #
    @28
    i1ff
    #
    syl
    ffvelrnda
    an32s
    eqeltrd
    adantllr
    wph
    @8
    @24
    @25
    @23
    c1
    caddc
    co
    #
    @13
    cfv
    #
    cle
    wbr
    @0
    @27
    @29
    @4
    @39
    cP
    cfv
    #
    cfv
    #
    @25
    @40
    cle
    wph
    @24
    @8
    @29
    @42
    cle
    wbr
    #
    @33
    @43
    vy
    cr
    @33
    @28
    @41
    @3
    wbr
    #
    @43
    vy
    cr
    wral
    wph
    @11
    @10
    c1
    caddc
    co
    #
    cP
    cfv
    #
    @3
    wbr
    #
    vn
    cn
    wral
    #
    @24
    @44
    wph
    c0p
    @11
    @3
    wbr
    #
    @47
    wa
    #
    vn
    cn
    wral
    @48
    itg2i1fseq.4
    @50
    @47
    vn
    cn
    @49
    @47
    simpr
    ralimi
    syl
    @47
    @44
    vn
    @23
    cn
    @30
    @11
    @28
    @46
    @41
    @3
    @31
    @30
    @45
    @39
    cP
    @10
    @23
    c1
    caddc
    oveq1
    fveq2d
    breq12d
    rspccva
    sylan
    @33
    vy
    cr
    cr
    @29
    @42
    cle
    cr
    @28
    @41
    cvv
    cvv
    @33
    @35
    @36
    @28
    cr
    wfn
    @37
    @38
    cr
    cr
    @28
    ffn
    3syl
    @33
    @41
    @34
    wcel
    #
    cr
    cr
    @41
    wf
    @41
    cr
    wfn
    wph
    cn
    @34
    cP
    wf
    @39
    cn
    wcel
    #
    @51
    @24
    itg2i1fseq.3
    @23
    peano2nn
    #
    cn
    @34
    @39
    cP
    ffvelrn
    syl2an
    @41
    i1ff
    cr
    cr
    @41
    ffn
    3syl
    cr
    cvv
    wcel
    #
    @33
    reex
    a1i
    #
    @55
    cr
    inidm
    #
    @33
    @8
    wa
    #
    @29
    eqidd
    @57
    @42
    eqidd
    ofrfval
    mpbid
    r19.21bi
    an32s
    @32
    @24
    @40
    @42
    wceq
    #
    @26
    @24
    @52
    @58
    @53
    vn
    @39
    @12
    @42
    cn
    @13
    @10
    @39
    wceq
    @4
    @11
    @41
    @10
    @39
    cP
    fveq2
    fveq1d
    @15
    @4
    @41
    fvex
    fvmpt
    syl
    adantl
    3brtr4d
    adantllr
    climub
    eqbrtrrd
    ralrimiva
    @1
    vy
    cr
    cr
    @5
    @6
    cle
    cr
    @2
    cF
    cvv
    cvv
    @1
    @2
    @34
    wcel
    cr
    cr
    @2
    wf
    @2
    cr
    wfn
    wph
    cn
    @34
    cM
    cP
    itg2i1fseq.3
    ffvelrnda
    @2
    i1ff
    cr
    cr
    @2
    ffn
    3syl
    wph
    cF
    cr
    wfn
    #
    @0
    wph
    cr
    cc0
    cpnf
    cicc
    co
    #
    cF
    wf
    #
    @59
    wph
    cr
    cc0
    cpnf
    cico
    co
    #
    cF
    wf
    @62
    @60
    wss
    @61
    itg2i1fseq.2
    cc0
    cpnf
    icossicc
    cr
    @62
    @60
    cF
    fss
    sylancl
    cr
    @60
    cF
    ffn
    syl
    adantr
    @54
    @1
    reex
    a1i
    #
    @63
    @56
    @9
    @5
    eqidd
    @9
    @6
    eqidd
    ofrfval
    mpbird
end
