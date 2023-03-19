include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cmul.mm"
include "cseq.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "cuz.mm"
include "eluzfz2.mm"
include "syl.mm"
include "cv.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "imbi2d.mm"
include "weq.mm"
include "eluzfz1.mm"
include "wa.mm"
include "cz.mm"
include "elfzelz.mm"
include "adantl.mm"
include "seq1.mm"
include "expcom.mm"
include "vtoclga.mm"
include "impcom.mm"
include "eqnetrd.mm"
include "cfzo.mm"
include "w3a.mm"
include "elfzouz.mm"
include "3ad2ant2.mm"
include "seqp1.mm"
include "cc.mm"
include "elfzofz.mm"
include "elfzuz.mm"
include "wss.mm"
include "elfzuz3.mm"
include "fzss2.mm"
include "sselda.mm"
include "sylan2.mm"
include "anassrs.mm"
include "mulcl.mm"
include "seqcl.mm"
include "3adant3.mm"
include "fzofzp1.mm"
include "eleq1d.mm"
include "simp3.mm"
include "mulne0d.mm"
include "3exp.mm"
include "com12.mm"
include "a2d.mm"
include "fzind2.mm"
include "mpcom.mm"

theorem prodfn0
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  assume prodfn0.1: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume prodfn0.2: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) e. CC )
  assume prodfn0.3: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) =/= 0 )

  disjoint F k
  disjoint k ph
  disjoint M k
  disjoint N k
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
  assert |- ( ph -> ( seq M ( x. , F ) ` N ) =/= 0 )

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
    cF
    cM
    cseq
    #
    cfv
    #
    cc0
    wne
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
    cc0
    wne
    #
    wi
    wph
    cM
    @2
    cfv
    #
    cc0
    wne
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
    cc0
    wne
    #
    wi
    wph
    @13
    c1
    caddc
    co
    #
    @2
    cfv
    #
    cc0
    wne
    #
    wi
    wph
    @4
    wi
    vm
    vn
    cN
    cM
    cN
    @7
    cM
    wceq
    #
    @9
    @11
    wph
    @19
    @8
    @10
    cc0
    @7
    cM
    @2
    fveq2
    neeq1d
    imbi2d
    vm
    vn
    weq
    #
    @9
    @15
    wph
    @20
    @8
    @14
    cc0
    @7
    @13
    @2
    fveq2
    neeq1d
    imbi2d
    @7
    @16
    wceq
    #
    @9
    @18
    wph
    @21
    @8
    @17
    cc0
    @7
    @16
    @2
    fveq2
    neeq1d
    imbi2d
    @7
    cN
    wceq
    #
    @9
    @4
    wph
    @22
    @8
    @3
    cc0
    @7
    cN
    @2
    fveq2
    neeq1d
    imbi2d
    @6
    cM
    @0
    wcel
    #
    @12
    cM
    cN
    eluzfz1
    wph
    @23
    @11
    wph
    @23
    wa
    #
    @10
    cM
    cF
    cfv
    #
    cc0
    @24
    cM
    cz
    wcel
    #
    @10
    @25
    wceq
    @23
    @26
    wph
    cM
    cM
    cN
    elfzelz
    adantl
    cmul
    cF
    cM
    seq1
    syl
    @23
    wph
    @25
    cc0
    wne
    #
    wph
    vk
    cv
    #
    cF
    cfv
    #
    cc0
    wne
    #
    wi
    #
    wph
    @27
    wi
    vk
    cM
    @0
    @28
    cM
    wceq
    #
    @30
    @27
    wph
    @32
    @29
    @25
    cc0
    @28
    cM
    cF
    fveq2
    neeq1d
    imbi2d
    wph
    @28
    @0
    wcel
    #
    @30
    prodfn0.3
    expcom
    #
    vtoclga
    impcom
    eqnetrd
    expcom
    syl
    @13
    cM
    cN
    cfzo
    co
    wcel
    #
    wph
    @15
    @18
    wph
    @35
    @15
    @18
    wi
    wph
    @35
    @15
    @18
    wph
    @35
    @15
    w3a
    #
    @17
    @14
    @16
    cF
    cfv
    #
    cmul
    co
    #
    cc0
    @36
    @13
    @5
    wcel
    #
    @17
    @38
    wceq
    @35
    wph
    @39
    @15
    @13
    cM
    cN
    elfzouz
    3ad2ant2
    cmul
    cF
    cM
    @13
    seqp1
    syl
    @36
    @14
    @37
    wph
    @35
    @14
    cc
    wcel
    #
    @15
    @35
    wph
    @13
    @0
    wcel
    #
    @40
    @13
    cM
    cN
    elfzofz
    wph
    @41
    wa
    #
    vk
    vx
    cmul
    cc
    cF
    cM
    @13
    @41
    @39
    wph
    @13
    cM
    cN
    elfzuz
    adantl
    wph
    @41
    @28
    cM
    @13
    cfz
    co
    #
    wcel
    #
    @29
    cc
    wcel
    #
    @41
    @44
    wa
    wph
    @33
    @45
    @41
    @43
    @0
    @28
    @41
    cN
    @13
    cuz
    cfv
    wcel
    @43
    @0
    wss
    @13
    cM
    cN
    elfzuz3
    @13
    cM
    cN
    fzss2
    syl
    sselda
    prodfn0.2
    sylan2
    anassrs
    @28
    cc
    wcel
    vx
    cv
    #
    cc
    wcel
    wa
    @28
    @46
    cmul
    co
    cc
    wcel
    @42
    @28
    @46
    mulcl
    adantl
    seqcl
    sylan2
    3adant3
    wph
    @35
    @37
    cc
    wcel
    #
    @15
    @35
    wph
    @47
    @35
    @16
    @0
    wcel
    #
    wph
    @47
    wi
    #
    cM
    cN
    @13
    fzofzp1
    #
    wph
    @45
    wi
    @49
    vk
    @16
    @0
    @28
    @16
    wceq
    #
    @45
    @47
    wph
    @51
    @29
    @37
    cc
    @28
    @16
    cF
    fveq2
    #
    eleq1d
    imbi2d
    wph
    @33
    @45
    prodfn0.2
    expcom
    vtoclga
    syl
    impcom
    3adant3
    wph
    @35
    @15
    simp3
    wph
    @35
    @37
    cc0
    wne
    #
    @15
    @35
    wph
    @48
    @53
    @50
    @48
    wph
    @53
    @31
    wph
    @53
    wi
    vk
    @16
    @0
    @51
    @30
    @53
    wph
    @51
    @29
    @37
    cc0
    @52
    neeq1d
    imbi2d
    @34
    vtoclga
    impcom
    sylan2
    3adant3
    mulne0d
    eqnetrd
    3exp
    com12
    a2d
    fzind2
    mpcom
end
