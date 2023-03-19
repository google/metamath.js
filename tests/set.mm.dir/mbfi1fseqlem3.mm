include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "cc0.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cfz.mm"
include "cv.mm"
include "cdiv.mm"
include "cmpt.mm"
include "crn.mm"
include "cfv.mm"
include "wf.mm"
include "cneg.mm"
include "cicc.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "wceq.mm"
include "clt.mm"
include "wb.mm"
include "cxp.mm"
include "cfl.mm"
include "wral.mm"
include "cpnf.mm"
include "cico.mm"
include "rge0ssre.mm"
include "simpr.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "sseldi.mm"
include "cn0.mm"
include "2nn.mm"
include "nnnn0.mm"
include "nnexpcl.mm"
include "sylancr.mm"
include "ad2antrl.mm"
include "nnred.mm"
include "remulcld.mm"
include "reflcl.mm"
include "syl.mm"
include "nndivred.mm"
include "ralrimivva.mm"
include "fmpt2.mm"
include "sylib.mm"
include "fovrn.mm"
include "syl3an1.mm"
include "3expa.mm"
include "nnre.mm"
include "ad2antlr.mm"
include "nngt0.mm"
include "jca.mm"
include "lemul1.mm"
include "syl3anc.mm"
include "biimpa.mm"
include "cuz.mm"
include "cz.mm"
include "simplr.mm"
include "adantr.mm"
include "fveq2d.mm"
include "simpl.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "ovex.mm"
include "ovmpt2a.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "ffvelrnda.mm"
include "elrege0.mm"
include "simpld.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "mulge0.mm"
include "syl12anc.mm"
include "flge0nn0.mm"
include "nn0cnd.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcan1d.mm"
include "eqtrd.mm"
include "eqeltrd.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "nnmulcl.mm"
include "mpdan.mm"
include "nnzd.mm"
include "elfz5.mm"
include "mpbird.mm"
include "oveq1.mm"
include "eqid.mm"
include "fvmpt.mm"
include "recnd.mm"
include "divcan4d.mm"
include "wfn.mm"
include "elfznn0.mm"
include "nn0red.mm"
include "adantl.mm"
include "nndivre.mm"
include "syl2anr.mm"
include "fmptd.mm"
include "ffn.mm"
include "fnfvelrn.mm"
include "eqeltrrd.mm"
include "wn.mm"
include "eluzfz2.mm"
include "ifclda.mm"
include "eluzfz1.mm"
include "nncn.mm"
include "nnne0.mm"
include "div0d.mm"
include "ifcld.mm"
include "mbfi1fseqlem2.mm"
include "feq1d.mm"

theorem mbfi1fseqlem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vm: setvar m
  let cF: class F
  let cG: class G
  let cJ: class J
  let vg: setvar g
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vz: setvar z
  assume mbfi1fseq.1: |- ( ph -> F e. MblFn )
  assume mbfi1fseq.2: |- ( ph -> F : RR --> ( 0 [,) +oo ) )
  assume mbfi1fseq.3: |- J = ( m e. NN , y e. RR |-> ( ( |_ ` ( ( F ` y ) x. ( 2 ^ m ) ) ) / ( 2 ^ m ) ) )
  assume mbfi1fseq.4: |- G = ( m e. NN |-> ( x e. RR |-> if ( x e. ( -u m [,] m ) , if ( ( m J x ) <_ m , ( m J x ) , m ) , 0 ) ) )

  disjoint m x
  disjoint m y
  disjoint F m
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint J m
  disjoint m ph
  disjoint ph x
  disjoint ph y
  disjoint A m
  disjoint A x
  disjoint A y
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint F g
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint m n
  disjoint m z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint G g
  disjoint G j
  disjoint G k
  disjoint G n
  disjoint j ph
  disjoint k ph
  disjoint n ph
  assert |- ( ( ph /\ A e. NN ) -> ( G ` A ) : RR --> ran ( m e. ( 0 ... ( A x. ( 2 ^ A ) ) ) |-> ( m / ( 2 ^ A ) ) ) )

  proof
    wph
    cA
    cn
    wcel
    #
    wa
    #
    cr
    vm
    cc0
    cA
    c2
    cA
    cexp
    co
    #
    cmul
    co
    #
    cfz
    co
    #
    vm
    cv
    #
    @2
    cdiv
    co
    #
    cmpt
    #
    crn
    #
    cA
    cG
    cfv
    #
    wf
    cr
    @8
    vx
    cr
    vx
    cv
    #
    cA
    cneg
    cA
    cicc
    co
    wcel
    #
    cA
    @10
    cJ
    co
    #
    cA
    cle
    wbr
    #
    @12
    cA
    cif
    #
    cc0
    cif
    #
    cmpt
    #
    wf
    @1
    vx
    cr
    @15
    @8
    @16
    @1
    @10
    cr
    wcel
    #
    wa
    #
    @11
    @14
    cc0
    @8
    @18
    @13
    @12
    cA
    @8
    @18
    @13
    wa
    #
    @12
    @2
    cmul
    co
    #
    @7
    cfv
    #
    @12
    @8
    @19
    @21
    @20
    @2
    cdiv
    co
    #
    @12
    @19
    @20
    @4
    wcel
    #
    @21
    @22
    wceq
    @19
    @23
    @20
    @3
    cle
    wbr
    #
    @18
    @13
    @24
    @18
    @12
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    cc0
    @2
    clt
    wbr
    #
    wa
    #
    @13
    @24
    wb
    wph
    @0
    @17
    @25
    wph
    cn
    cr
    cxp
    cr
    cJ
    wf
    #
    @0
    @17
    @25
    wph
    vy
    cv
    #
    cF
    cfv
    #
    c2
    @5
    cexp
    co
    #
    cmul
    co
    #
    cfl
    cfv
    #
    @33
    cdiv
    co
    #
    cr
    wcel
    #
    vy
    cr
    wral
    vm
    cn
    wral
    @30
    wph
    @37
    vm
    vy
    cn
    cr
    wph
    @5
    cn
    wcel
    #
    @31
    cr
    wcel
    #
    wa
    #
    wa
    #
    @35
    @33
    @41
    @34
    cr
    wcel
    @35
    cr
    wcel
    @41
    @32
    @33
    @41
    cc0
    cpnf
    cico
    co
    #
    cr
    @32
    rge0ssre
    wph
    cr
    @42
    cF
    wf
    #
    @39
    @32
    @42
    wcel
    @40
    mbfi1fseq.2
    @38
    @39
    simpr
    cr
    @42
    @31
    cF
    ffvelrn
    syl2an
    sseldi
    @41
    @33
    @38
    @33
    cn
    wcel
    #
    wph
    @39
    @38
    c2
    cn
    wcel
    #
    @5
    cn0
    wcel
    @44
    2nn
    @5
    nnnn0
    c2
    @5
    nnexpcl
    sylancr
    ad2antrl
    #
    nnred
    remulcld
    @34
    reflcl
    syl
    @46
    nndivred
    ralrimivva
    vm
    vy
    cn
    cr
    @36
    cr
    cJ
    mbfi1fseq.3
    fmpt2
    sylib
    cA
    @10
    cr
    cn
    cr
    cJ
    fovrn
    syl3an1
    3expa
    #
    @0
    @26
    wph
    @17
    cA
    nnre
    ad2antlr
    #
    @18
    @2
    cn
    wcel
    #
    @29
    @0
    @49
    wph
    @17
    @0
    @45
    cA
    cn0
    wcel
    @49
    2nn
    cA
    nnnn0
    c2
    cA
    nnexpcl
    sylancr
    #
    ad2antlr
    #
    @49
    @27
    @28
    @2
    nnre
    @2
    nngt0
    jca
    syl
    @12
    cA
    @2
    lemul1
    syl3anc
    biimpa
    @19
    @20
    cc0
    cuz
    cfv
    #
    wcel
    @3
    cz
    wcel
    @23
    @24
    wb
    @19
    @20
    cn0
    @52
    @19
    @20
    @10
    cF
    cfv
    #
    @2
    cmul
    co
    #
    cfl
    cfv
    #
    cn0
    @19
    @20
    @55
    @2
    cdiv
    co
    #
    @2
    cmul
    co
    @55
    @19
    @12
    @56
    @2
    cmul
    @19
    @0
    @17
    @12
    @56
    wceq
    @18
    @0
    @13
    wph
    @0
    @17
    simplr
    adantr
    @1
    @17
    @13
    simplr
    vm
    vy
    cA
    @10
    cn
    cr
    @36
    @56
    cJ
    @5
    cA
    wceq
    #
    @31
    @10
    wceq
    #
    wa
    #
    @35
    @55
    @33
    @2
    cdiv
    @59
    @34
    @54
    cfl
    @59
    @32
    @53
    @33
    @2
    cmul
    @59
    @31
    @10
    cF
    @57
    @58
    simpr
    fveq2d
    @59
    @5
    cA
    c2
    cexp
    @57
    @58
    simpl
    oveq2d
    #
    oveq12d
    fveq2d
    @60
    oveq12d
    mbfi1fseq.3
    @55
    @2
    cdiv
    ovex
    ovmpt2a
    syl2anc
    oveq1d
    @19
    @55
    @2
    @19
    @55
    @18
    @55
    cn0
    wcel
    #
    @13
    @18
    @54
    cr
    wcel
    cc0
    @54
    cle
    wbr
    #
    @61
    @18
    @53
    @2
    @18
    @53
    cr
    wcel
    #
    cc0
    @53
    cle
    wbr
    #
    @18
    @53
    @42
    wcel
    @63
    @64
    wa
    #
    @1
    cr
    @42
    @10
    cF
    wph
    @43
    @0
    mbfi1fseq.2
    adantr
    ffvelrnda
    @53
    elrege0
    sylib
    #
    simpld
    @18
    @2
    @51
    nnred
    #
    remulcld
    @18
    @65
    @27
    cc0
    @2
    cle
    wbr
    @62
    @66
    @67
    @18
    @2
    @18
    @2
    @51
    nnnn0d
    nn0ge0d
    @53
    @2
    mulge0
    syl12anc
    @54
    flge0nn0
    syl2anc
    adantr
    #
    nn0cnd
    @19
    @2
    @18
    @49
    @13
    @51
    adantr
    #
    nncnd
    #
    @19
    @2
    @69
    nnne0d
    #
    divcan1d
    eqtrd
    @68
    eqeltrd
    nn0uz
    syl6eleq
    @19
    @3
    @18
    @3
    cn
    wcel
    #
    @13
    @0
    @72
    wph
    @17
    @0
    @49
    @72
    @50
    cA
    @2
    nnmulcl
    mpdan
    ad2antlr
    #
    adantr
    nnzd
    @20
    cc0
    @3
    elfz5
    syl2anc
    mpbird
    #
    vm
    @20
    @6
    @22
    @4
    @7
    @5
    @20
    @2
    cdiv
    oveq1
    @7
    eqid
    #
    @20
    @2
    cdiv
    ovex
    fvmpt
    syl
    @19
    @12
    @2
    @19
    @12
    @18
    @25
    @13
    @47
    adantr
    recnd
    @70
    @71
    divcan4d
    eqtrd
    @19
    @7
    @4
    wfn
    #
    @23
    @21
    @8
    wcel
    @18
    @76
    @13
    @1
    @76
    @17
    @1
    @4
    cr
    @7
    wf
    @76
    @1
    vm
    @4
    @6
    cr
    @7
    @5
    @4
    wcel
    #
    @5
    cr
    wcel
    @49
    @6
    cr
    wcel
    @1
    @77
    @5
    @5
    @3
    elfznn0
    nn0red
    @0
    @49
    wph
    @50
    adantl
    @5
    @2
    nndivre
    syl2anr
    @75
    fmptd
    @4
    cr
    @7
    ffn
    syl
    adantr
    #
    adantr
    @74
    @4
    @20
    @7
    fnfvelrn
    syl2anc
    eqeltrrd
    @18
    cA
    @8
    wcel
    @13
    wn
    @18
    @3
    @7
    cfv
    #
    cA
    @8
    @18
    @79
    @3
    @2
    cdiv
    co
    #
    cA
    @18
    @3
    @4
    wcel
    #
    @79
    @80
    wceq
    @18
    @3
    @52
    wcel
    #
    @81
    @18
    @3
    cn0
    @52
    @18
    @3
    @73
    nnnn0d
    nn0uz
    syl6eleq
    #
    cc0
    @3
    eluzfz2
    syl
    #
    vm
    @3
    @6
    @80
    @4
    @7
    @5
    @3
    @2
    cdiv
    oveq1
    @75
    @3
    @2
    cdiv
    ovex
    fvmpt
    syl
    @18
    cA
    @2
    @18
    cA
    @48
    recnd
    @18
    @2
    @51
    nncnd
    @18
    @2
    @51
    nnne0d
    divcan4d
    eqtrd
    @18
    @76
    @81
    @79
    @8
    wcel
    @78
    @84
    @4
    @3
    @7
    fnfvelrn
    syl2anc
    eqeltrrd
    adantr
    ifclda
    @18
    cc0
    @7
    cfv
    #
    cc0
    @8
    @18
    @85
    cc0
    @2
    cdiv
    co
    #
    cc0
    @18
    cc0
    @4
    wcel
    #
    @85
    @86
    wceq
    @18
    @82
    @87
    @83
    cc0
    @3
    eluzfz1
    syl
    #
    vm
    cc0
    @6
    @86
    @4
    @7
    @5
    cc0
    @2
    cdiv
    oveq1
    @75
    cc0
    @2
    cdiv
    ovex
    fvmpt
    syl
    @18
    @49
    @86
    cc0
    wceq
    @51
    @49
    @2
    @2
    nncn
    @2
    nnne0
    div0d
    syl
    eqtrd
    @18
    @76
    @87
    @85
    @8
    wcel
    @78
    @88
    @4
    cc0
    @7
    fnfvelrn
    syl2anc
    eqeltrrd
    ifcld
    @16
    eqid
    fmptd
    @1
    cr
    @8
    @9
    @16
    @0
    @9
    @16
    wceq
    wph
    wph
    vx
    vy
    cA
    vm
    cF
    cG
    cJ
    mbfi1fseq.1
    mbfi1fseq.2
    mbfi1fseq.3
    mbfi1fseq.4
    mbfi1fseqlem2
    adantl
    feq1d
    mpbird
end
