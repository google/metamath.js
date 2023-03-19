include "cv.mm"
include "wfn.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "cmpt.mm"
include "com.mm"
include "cen.mm"
include "wbr.mm"
include "cvv.mm"
include "relen.mm"
include "brrelexi.mm"
include "mptexg.mm"
include "mp2b.mm"
include "wceq.mm"
include "wf1o.mm"
include "bren.mm"
include "mpbi.mm"
include "ccnv.mm"
include "ccom.mm"
include "axcc2.mm"
include "w3a.mm"
include "wf.mm"
include "f1of.mm"
include "fnfco.mm"
include "sylan2.mm"
include "adantlr.mm"
include "3adant1.mm"
include "nfmpt1.mm"
include "nfeq2.mm"
include "nfv.mm"
include "nf3an.mm"
include "ffvelrnda.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl.mm"
include "3ad2antl3.mm"
include "f1ocnv.mm"
include "fvco3.mm"
include "sylan.mm"
include "syldan.mm"
include "f1ocnvfv1.mm"
include "fveq2d.mm"
include "fveq1.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "sylan9eq.mm"
include "3adant2.mm"
include "3eqtrd.mm"
include "3expa.mm"
include "3adantl2.mm"
include "3ad2ant3.mm"
include "eleq1d.mm"
include "eleq2d.mm"
include "bitr3d.mm"
include "sylibd.mm"
include "ex.mm"
include "com23.mm"
include "3exp.mm"
include "com34.mm"
include "imp32.mm"
include "3impia.mm"
include "ralrimi.mm"
include "vex.mm"
include "coex.mm"
include "fneq1.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "spcev.mm"
include "syl2anc.mm"
include "exlimdv.mm"
include "mpi.mm"
include "vtocle.mm"

theorem axcc3
  let vf: setvar f
  let vn: setvar n
  let cF: class F
  let cN: class N
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vm: setvar m
  assume axcc3.1: |- F e. _V
  assume axcc3.2: |- N ~~ _om

  disjoint F f
  disjoint N f
  disjoint N n
  disjoint f n
  disjoint F g
  disjoint F h
  disjoint F k
  disjoint F m
  disjoint f g
  disjoint f h
  disjoint f k
  disjoint f m
  disjoint g h
  disjoint g k
  disjoint g m
  disjoint h k
  disjoint h m
  disjoint k m
  disjoint N g
  disjoint N h
  disjoint N k
  disjoint N m
  disjoint g n
  disjoint h n
  disjoint k n
  disjoint m n
  assert |- E. f ( f Fn N /\ A. n e. N ( F =/= (/) -> ( f ` n ) e. F ) )

  proof
    vf
    cv
    #
    cN
    wfn
    #
    cF
    c0
    wne
    #
    vn
    cv
    #
    @0
    cfv
    #
    cF
    wcel
    #
    wi
    #
    vn
    cN
    wral
    #
    wa
    #
    vf
    wex
    #
    vk
    vn
    cN
    cF
    cmpt
    #
    cN
    com
    cen
    wbr
    #
    cN
    cvv
    wcel
    @10
    cvv
    wcel
    axcc3.2
    cN
    com
    cen
    relen
    brrelexi
    vn
    cN
    cF
    cvv
    mptexg
    mp2b
    vk
    cv
    #
    @10
    wceq
    #
    cN
    com
    vh
    cv
    #
    wf1o
    #
    vh
    wex
    #
    @9
    @11
    @16
    axcc3.2
    cN
    com
    vh
    bren
    mpbi
    @13
    @15
    @9
    vh
    @13
    vg
    cv
    #
    com
    wfn
    #
    vm
    cv
    #
    @12
    @14
    ccnv
    #
    ccom
    #
    cfv
    #
    c0
    wne
    #
    @19
    @17
    cfv
    #
    @22
    wcel
    #
    wi
    #
    vm
    com
    wral
    #
    wa
    #
    vg
    wex
    @15
    @9
    wi
    #
    vg
    vm
    @21
    axcc2
    @13
    @28
    @29
    vg
    @13
    @28
    @15
    @9
    @13
    @28
    @15
    w3a
    #
    @17
    @14
    ccom
    #
    cN
    wfn
    #
    @2
    @3
    @31
    cfv
    #
    cF
    wcel
    #
    wi
    #
    vn
    cN
    wral
    #
    @9
    @28
    @15
    @32
    @13
    @18
    @15
    @32
    @27
    @15
    @18
    cN
    com
    @14
    wf
    #
    @32
    cN
    com
    @14
    f1of
    #
    com
    cN
    @17
    @14
    fnfco
    sylan2
    adantlr
    3adant1
    @30
    @35
    vn
    cN
    @13
    @28
    @15
    vn
    vn
    @12
    @10
    vn
    cN
    cF
    nfmpt1
    nfeq2
    @28
    vn
    nfv
    @15
    vn
    nfv
    nf3an
    @13
    @28
    @15
    @3
    cN
    wcel
    #
    @35
    wi
    #
    @13
    @18
    @27
    @15
    @40
    wi
    @13
    @18
    @15
    @27
    @40
    @13
    @18
    @15
    @27
    @40
    wi
    @13
    @18
    @15
    w3a
    #
    @39
    @27
    @35
    @41
    @39
    @27
    @35
    wi
    @41
    @39
    wa
    #
    @27
    @3
    @14
    cfv
    #
    @21
    cfv
    #
    c0
    wne
    #
    @43
    @17
    cfv
    #
    @44
    wcel
    #
    wi
    #
    @35
    @15
    @13
    @39
    @27
    @48
    wi
    #
    @18
    @15
    @39
    wa
    #
    @43
    com
    wcel
    #
    @49
    @15
    cN
    com
    @3
    @14
    @38
    ffvelrnda
    #
    @26
    @48
    vm
    @43
    com
    @19
    @43
    wceq
    #
    @23
    @45
    @25
    @47
    @53
    @22
    @44
    c0
    @19
    @43
    @21
    fveq2
    #
    neeq1d
    @53
    @24
    @46
    @22
    @44
    @19
    @43
    @17
    fveq2
    @54
    eleq12d
    imbi12d
    rspcv
    syl
    3ad2antl3
    @42
    @45
    @2
    @47
    @34
    @42
    @44
    cF
    c0
    @13
    @15
    @39
    @44
    cF
    wceq
    #
    @18
    @13
    @15
    @39
    @55
    @13
    @15
    @39
    w3a
    @44
    @43
    @20
    cfv
    #
    @12
    cfv
    #
    @3
    @12
    cfv
    #
    cF
    @15
    @39
    @44
    @57
    wceq
    #
    @13
    @15
    @39
    @51
    @59
    @52
    @15
    com
    cN
    @20
    wf
    #
    @51
    @59
    @15
    com
    cN
    @20
    wf1o
    @60
    cN
    com
    @14
    f1ocnv
    com
    cN
    @20
    f1of
    syl
    com
    cN
    @43
    @12
    @20
    fvco3
    sylan
    syldan
    3adant1
    @15
    @39
    @57
    @58
    wceq
    @13
    @50
    @56
    @3
    @12
    cN
    com
    @3
    @14
    f1ocnvfv1
    fveq2d
    3adant1
    @13
    @39
    @58
    cF
    wceq
    @15
    @13
    @39
    @58
    @3
    @10
    cfv
    #
    cF
    @3
    @12
    @10
    fveq1
    @39
    cF
    cvv
    wcel
    @61
    cF
    wceq
    axcc3.1
    vn
    cN
    cF
    cvv
    @10
    @10
    eqid
    fvmpt2
    mpan2
    sylan9eq
    3adant2
    3eqtrd
    3expa
    3adantl2
    #
    neeq1d
    @42
    @33
    @44
    wcel
    @47
    @34
    @42
    @33
    @46
    @44
    @41
    @37
    @39
    @33
    @46
    wceq
    @15
    @13
    @37
    @18
    @38
    3ad2ant3
    cN
    com
    @3
    @17
    @14
    fvco3
    sylan
    eleq1d
    @42
    @44
    cF
    @33
    @62
    eleq2d
    bitr3d
    imbi12d
    sylibd
    ex
    com23
    3exp
    com34
    imp32
    3impia
    ralrimi
    @8
    @32
    @36
    wa
    vf
    @31
    @17
    @14
    vg
    vex
    vh
    vex
    coex
    @0
    @31
    wceq
    #
    @1
    @32
    @7
    @36
    cN
    @0
    @31
    fneq1
    @63
    @6
    @35
    vn
    cN
    @63
    @5
    @34
    @2
    @63
    @4
    @33
    cF
    @3
    @0
    @31
    fveq1
    eleq1d
    imbi2d
    ralbidv
    anbi12d
    spcev
    syl2anc
    3exp
    exlimdv
    mpi
    exlimdv
    mpi
    vtocle
end
