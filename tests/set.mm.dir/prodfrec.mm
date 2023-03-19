include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cmul.mm"
include "cseq.mm"
include "cfv.mm"
include "c1.mm"
include "cdiv.mm"
include "wceq.mm"
include "cuz.mm"
include "eluzfz2.mm"
include "syl.mm"
include "cv.mm"
include "wi.mm"
include "caddc.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "eluzfz1.mm"
include "expcom.mm"
include "vtoclga.mm"
include "mpcom.mm"
include "cz.mm"
include "eluzel2.mm"
include "seq1.mm"
include "3eqtr4d.mm"
include "a1i.mm"
include "cfzo.mm"
include "w3a.mm"
include "oveq1.mm"
include "3ad2ant3.mm"
include "wa.mm"
include "fzofzp1.mm"
include "impcom.mm"
include "1cnd.mm"
include "cc.mm"
include "elfzouz.mm"
include "adantl.mm"
include "wss.mm"
include "elfzouz2.mm"
include "fzss2.mm"
include "sselda.mm"
include "sylan2.mm"
include "anassrs.mm"
include "mulcl.mm"
include "seqcl.mm"
include "eleq1d.mm"
include "cc0.mm"
include "wne.mm"
include "prodfn0.mm"
include "neeq1d.mm"
include "divmuldivd.mm"
include "1t1e1.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "3adant3.mm"
include "seqp1.mm"
include "3ad2ant2.mm"
include "3exp.mm"
include "com12.mm"
include "a2d.mm"
include "fzind2.mm"

theorem prodfrec
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  assume prodfn0.1: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume prodfn0.2: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) e. CC )
  assume prodfn0.3: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) =/= 0 )
  assume prodfrec.4: |- ( ( ph /\ k e. ( M ... N ) ) -> ( G ` k ) = ( 1 / ( F ` k ) ) )

  disjoint F k
  disjoint k ph
  disjoint M k
  disjoint N k
  disjoint G k
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint k n
  disjoint k x
  disjoint M m
  disjoint m n
  disjoint M n
  disjoint m ph
  disjoint M x
  disjoint N m
  disjoint N n
  disjoint n ph
  disjoint n x
  disjoint N x
  disjoint ph x
  disjoint G m
  disjoint G n
  assert |- ( ph -> ( seq M ( x. , G ) ` N ) = ( 1 / ( seq M ( x. , F ) ` N ) ) )

  proof
    cN
    cM
    cN
    cfz
    co
    #
    wcel
    #
    wph
    cN
    cmul
    cG
    cM
    cseq
    #
    cfv
    #
    c1
    cN
    cmul
    cF
    cM
    cseq
    #
    cfv
    #
    cdiv
    co
    #
    wceq
    #
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    @1
    prodfn0.1
    cM
    cN
    eluzfz2
    syl
    wph
    vm
    cv
    #
    @2
    cfv
    #
    c1
    @10
    @4
    cfv
    #
    cdiv
    co
    #
    wceq
    #
    wi
    wph
    cM
    @2
    cfv
    #
    c1
    cM
    @4
    cfv
    #
    cdiv
    co
    #
    wceq
    #
    wi
    #
    wph
    vn
    cv
    #
    @2
    cfv
    #
    c1
    @20
    @4
    cfv
    #
    cdiv
    co
    #
    wceq
    #
    wi
    wph
    @20
    c1
    caddc
    co
    #
    @2
    cfv
    #
    c1
    @25
    @4
    cfv
    #
    cdiv
    co
    #
    wceq
    #
    wi
    wph
    @7
    wi
    vm
    vn
    cN
    cM
    cN
    @10
    cM
    wceq
    #
    @14
    @18
    wph
    @30
    @11
    @15
    @13
    @17
    @10
    cM
    @2
    fveq2
    @30
    @12
    @16
    c1
    cdiv
    @10
    cM
    @4
    fveq2
    oveq2d
    eqeq12d
    imbi2d
    vm
    vn
    weq
    #
    @14
    @24
    wph
    @31
    @11
    @21
    @13
    @23
    @10
    @20
    @2
    fveq2
    @31
    @12
    @22
    c1
    cdiv
    @10
    @20
    @4
    fveq2
    oveq2d
    eqeq12d
    imbi2d
    @10
    @25
    wceq
    #
    @14
    @29
    wph
    @32
    @11
    @26
    @13
    @28
    @10
    @25
    @2
    fveq2
    @32
    @12
    @27
    c1
    cdiv
    @10
    @25
    @4
    fveq2
    oveq2d
    eqeq12d
    imbi2d
    @10
    cN
    wceq
    #
    @14
    @7
    wph
    @33
    @11
    @3
    @13
    @6
    @10
    cN
    @2
    fveq2
    @33
    @12
    @5
    c1
    cdiv
    @10
    cN
    @4
    fveq2
    oveq2d
    eqeq12d
    imbi2d
    @19
    @9
    wph
    cM
    cG
    cfv
    #
    c1
    cM
    cF
    cfv
    #
    cdiv
    co
    #
    @15
    @17
    cM
    @0
    wcel
    #
    wph
    @34
    @36
    wceq
    #
    wph
    @9
    @37
    prodfn0.1
    cM
    cN
    eluzfz1
    syl
    wph
    vk
    cv
    #
    cG
    cfv
    #
    c1
    @39
    cF
    cfv
    #
    cdiv
    co
    #
    wceq
    #
    wi
    #
    wph
    @38
    wi
    vk
    cM
    @0
    @39
    cM
    wceq
    #
    @43
    @38
    wph
    @45
    @40
    @34
    @42
    @36
    @39
    cM
    cG
    fveq2
    @45
    @41
    @35
    c1
    cdiv
    @39
    cM
    cF
    fveq2
    oveq2d
    eqeq12d
    imbi2d
    wph
    @39
    @0
    wcel
    #
    @43
    prodfrec.4
    expcom
    #
    vtoclga
    mpcom
    wph
    cM
    cz
    wcel
    #
    @15
    @34
    wceq
    wph
    @9
    @48
    prodfn0.1
    cM
    cN
    eluzel2
    syl
    #
    cmul
    cG
    cM
    seq1
    syl
    wph
    @16
    @35
    c1
    cdiv
    wph
    @48
    @16
    @35
    wceq
    @49
    cmul
    cF
    cM
    seq1
    syl
    oveq2d
    3eqtr4d
    a1i
    @20
    cM
    cN
    cfzo
    co
    wcel
    #
    wph
    @24
    @29
    wph
    @50
    @24
    @29
    wi
    wph
    @50
    @24
    @29
    wph
    @50
    @24
    w3a
    #
    @21
    @25
    cG
    cfv
    #
    cmul
    co
    #
    c1
    @22
    @25
    cF
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    @26
    @28
    @51
    @53
    @23
    @52
    cmul
    co
    #
    @56
    @24
    wph
    @53
    @57
    wceq
    @50
    @21
    @23
    @52
    cmul
    oveq1
    3ad2ant3
    wph
    @50
    @57
    @56
    wceq
    @24
    wph
    @50
    wa
    #
    @57
    @23
    c1
    @54
    cdiv
    co
    #
    cmul
    co
    #
    @56
    @58
    @52
    @59
    @23
    cmul
    @50
    wph
    @52
    @59
    wceq
    #
    @50
    @25
    @0
    wcel
    #
    wph
    @61
    wi
    #
    cM
    cN
    @20
    fzofzp1
    #
    @44
    @63
    vk
    @25
    @0
    @39
    @25
    wceq
    #
    @43
    @61
    wph
    @65
    @40
    @52
    @42
    @59
    @39
    @25
    cG
    fveq2
    @65
    @41
    @54
    c1
    cdiv
    @39
    @25
    cF
    fveq2
    #
    oveq2d
    eqeq12d
    imbi2d
    @47
    vtoclga
    syl
    impcom
    oveq2d
    @58
    @60
    c1
    c1
    cmul
    co
    #
    @55
    cdiv
    co
    @56
    @58
    c1
    @22
    c1
    @54
    @58
    1cnd
    #
    @58
    vk
    vx
    cmul
    cc
    cF
    cM
    @20
    @50
    @20
    @8
    wcel
    #
    wph
    @20
    cM
    cN
    elfzouz
    #
    adantl
    #
    wph
    @50
    @39
    cM
    @20
    cfz
    co
    #
    wcel
    #
    @41
    cc
    wcel
    #
    @50
    @73
    wa
    #
    wph
    @46
    @74
    @50
    @72
    @0
    @39
    @50
    cN
    @20
    cuz
    cfv
    wcel
    @72
    @0
    wss
    @20
    cM
    cN
    elfzouz2
    @20
    cM
    cN
    fzss2
    syl
    sselda
    #
    prodfn0.2
    sylan2
    anassrs
    #
    @39
    cc
    wcel
    vx
    cv
    #
    cc
    wcel
    wa
    @39
    @78
    cmul
    co
    cc
    wcel
    @58
    @39
    @78
    mulcl
    adantl
    seqcl
    @68
    @50
    wph
    @54
    cc
    wcel
    #
    @50
    @62
    wph
    @79
    wi
    #
    @64
    wph
    @74
    wi
    @80
    vk
    @25
    @0
    @65
    @74
    @79
    wph
    @65
    @41
    @54
    cc
    @66
    eleq1d
    imbi2d
    wph
    @46
    @74
    prodfn0.2
    expcom
    vtoclga
    syl
    impcom
    @58
    vk
    cF
    cM
    @20
    @71
    @77
    wph
    @50
    @73
    @41
    cc0
    wne
    #
    @75
    wph
    @46
    @81
    @76
    prodfn0.3
    sylan2
    anassrs
    prodfn0
    @50
    wph
    @54
    cc0
    wne
    #
    @50
    @62
    wph
    @82
    wi
    #
    @64
    wph
    @81
    wi
    @83
    vk
    @25
    @0
    @65
    @81
    @82
    wph
    @65
    @41
    @54
    cc0
    @66
    neeq1d
    imbi2d
    wph
    @46
    @81
    prodfn0.3
    expcom
    vtoclga
    syl
    impcom
    divmuldivd
    @67
    c1
    @55
    cdiv
    1t1e1
    oveq1i
    syl6eq
    eqtrd
    3adant3
    eqtrd
    @50
    wph
    @26
    @53
    wceq
    #
    @24
    @50
    @69
    @84
    @70
    cmul
    cG
    cM
    @20
    seqp1
    syl
    3ad2ant2
    @50
    wph
    @28
    @56
    wceq
    @24
    @50
    @27
    @55
    c1
    cdiv
    @50
    @69
    @27
    @55
    wceq
    @70
    cmul
    cF
    cM
    @20
    seqp1
    syl
    oveq2d
    3ad2ant2
    3eqtr4d
    3exp
    com12
    a2d
    fzind2
    mpcom
end
