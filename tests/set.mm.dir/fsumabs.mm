include "wss.mm"
include "csu.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "ssid.mm"
include "cfn.mm"
include "wcel.mm"
include "wi.mm"
include "cv.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "sseq1.mm"
include "sumeq1.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "cc0.mm"
include "0le0.mm"
include "sum0.mm"
include "fveq2i.mm"
include "abs0.mm"
include "eqtri.mm"
include "3brtr4i.mm"
include "2a1i.mm"
include "wn.mm"
include "wa.mm"
include "ssun1.mm"
include "sstr.mm"
include "mpan.mm"
include "imim1i.mm"
include "csb.mm"
include "caddc.mm"
include "co.mm"
include "simpll.mm"
include "syl.mm"
include "simpr.mm"
include "unssad.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "cc.mm"
include "sselda.mm"
include "sylan.mm"
include "syldan.mm"
include "fsumcl.mm"
include "abscld.mm"
include "fsumrecl.mm"
include "wral.mm"
include "unssbd.mm"
include "vex.mm"
include "snss.mm"
include "sylibr.mm"
include "ralrimiva.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "rspc.mm"
include "sylc.mm"
include "leadd1d.mm"
include "cin.mm"
include "simplr.mm"
include "disjsn.mm"
include "eqidd.mm"
include "recnd.mm"
include "fsumsplit.mm"
include "cvv.mm"
include "csbfv2g.mm"
include "ax-mp.mm"
include "syl5eqel.mm"
include "sumsns.mm"
include "sylancr.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "breq2d.mm"
include "bitr4d.mm"
include "abstrid.mm"
include "eqbrtrd.mm"
include "cr.mm"
include "readdcld.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "sylbid.mm"
include "ex.mm"
include "a2d.mm"
include "syl5.mm"
include "expcom.mm"
include "adantl.mm"
include "findcard2s.mm"
include "mpcom.mm"
include "mpi.mm"

theorem fsumabs
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  assume fsumabs.1: |- ( ph -> A e. Fin )
  assume fsumabs.2: |- ( ( ph /\ k e. A ) -> B e. CC )

  disjoint A k
  disjoint k ph
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint ph w
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( abs ` sum_ k e. A B ) <_ sum_ k e. A ( abs ` B ) )

  proof
    wph
    cA
    cA
    wss
    #
    cA
    cB
    vk
    csu
    #
    cabs
    cfv
    #
    cA
    cB
    cabs
    cfv
    #
    vk
    csu
    #
    cle
    wbr
    #
    cA
    ssid
    cA
    cfn
    wcel
    #
    wph
    @0
    @5
    wi
    #
    fsumabs.1
    wph
    vw
    cv
    #
    cA
    wss
    #
    @8
    cB
    vk
    csu
    #
    cabs
    cfv
    #
    @8
    @3
    vk
    csu
    #
    cle
    wbr
    #
    wi
    #
    wi
    wph
    c0
    cA
    wss
    #
    c0
    cB
    vk
    csu
    #
    cabs
    cfv
    #
    c0
    @3
    vk
    csu
    #
    cle
    wbr
    #
    wi
    #
    wi
    wph
    vx
    cv
    #
    cA
    wss
    #
    @21
    cB
    vk
    csu
    #
    cabs
    cfv
    #
    @21
    @3
    vk
    csu
    #
    cle
    wbr
    #
    wi
    #
    wi
    #
    wph
    @21
    vy
    cv
    #
    csn
    #
    cun
    #
    cA
    wss
    #
    @31
    cB
    vk
    csu
    #
    cabs
    cfv
    #
    @31
    @3
    vk
    csu
    #
    cle
    wbr
    #
    wi
    #
    wi
    #
    wph
    @7
    wi
    vw
    vx
    vy
    cA
    @8
    c0
    wceq
    #
    @14
    @20
    wph
    @39
    @9
    @15
    @13
    @19
    @8
    c0
    cA
    sseq1
    @39
    @11
    @17
    @12
    @18
    cle
    @39
    @10
    @16
    cabs
    @8
    c0
    cB
    vk
    sumeq1
    fveq2d
    @8
    c0
    @3
    vk
    sumeq1
    breq12d
    imbi12d
    imbi2d
    @8
    @21
    wceq
    #
    @14
    @27
    wph
    @40
    @9
    @22
    @13
    @26
    @8
    @21
    cA
    sseq1
    @40
    @11
    @24
    @12
    @25
    cle
    @40
    @10
    @23
    cabs
    @8
    @21
    cB
    vk
    sumeq1
    fveq2d
    @8
    @21
    @3
    vk
    sumeq1
    breq12d
    imbi12d
    imbi2d
    @8
    @31
    wceq
    #
    @14
    @37
    wph
    @41
    @9
    @32
    @13
    @36
    @8
    @31
    cA
    sseq1
    @41
    @11
    @34
    @12
    @35
    cle
    @41
    @10
    @33
    cabs
    @8
    @31
    cB
    vk
    sumeq1
    fveq2d
    @8
    @31
    @3
    vk
    sumeq1
    breq12d
    imbi12d
    imbi2d
    @8
    cA
    wceq
    #
    @14
    @7
    wph
    @42
    @9
    @0
    @13
    @5
    @8
    cA
    cA
    sseq1
    @42
    @11
    @2
    @12
    @4
    cle
    @42
    @10
    @1
    cabs
    @8
    cA
    cB
    vk
    sumeq1
    fveq2d
    @8
    cA
    @3
    vk
    sumeq1
    breq12d
    imbi12d
    imbi2d
    @19
    wph
    @15
    cc0
    cc0
    @17
    @18
    cle
    0le0
    @17
    cc0
    cabs
    cfv
    cc0
    @16
    cc0
    cabs
    cB
    vk
    sum0
    fveq2i
    abs0
    eqtri
    @3
    vk
    sum0
    3brtr4i
    2a1i
    @29
    @21
    wcel
    wn
    #
    @28
    @38
    wi
    @21
    cfn
    wcel
    #
    @43
    wph
    @27
    @37
    wph
    @43
    @27
    @37
    wi
    @27
    @32
    @26
    wi
    wph
    @43
    wa
    #
    @37
    @32
    @22
    @26
    @21
    @31
    wss
    @32
    @22
    @21
    @30
    ssun1
    @21
    @31
    cA
    sstr
    mpan
    imim1i
    @45
    @32
    @26
    @36
    @45
    @32
    @26
    @36
    wi
    @45
    @32
    wa
    #
    @26
    @24
    vk
    @29
    cB
    csb
    #
    cabs
    cfv
    #
    caddc
    co
    #
    @35
    cle
    wbr
    #
    @36
    @46
    @26
    @49
    @25
    @48
    caddc
    co
    #
    cle
    wbr
    @50
    @46
    @24
    @25
    @48
    @46
    @23
    @46
    @21
    cB
    vk
    @46
    @6
    @22
    @44
    @46
    wph
    @6
    wph
    @43
    @32
    simpll
    #
    fsumabs.1
    syl
    #
    @46
    @21
    @30
    cA
    @45
    @32
    simpr
    #
    unssad
    #
    cA
    @21
    ssfi
    syl2anc
    #
    @46
    vk
    cv
    #
    @21
    wcel
    #
    @57
    cA
    wcel
    #
    cB
    cc
    wcel
    #
    @46
    @21
    cA
    @57
    @55
    sselda
    @46
    wph
    @59
    @60
    @52
    fsumabs.2
    sylan
    #
    syldan
    #
    fsumcl
    #
    abscld
    #
    @46
    @21
    @3
    vk
    @56
    @46
    @58
    wa
    cB
    @62
    abscld
    fsumrecl
    @46
    @47
    @46
    @29
    cA
    wcel
    #
    @60
    vk
    cA
    wral
    #
    @47
    cc
    wcel
    #
    @46
    @30
    cA
    wss
    @65
    @46
    @21
    @30
    cA
    @54
    unssbd
    @29
    cA
    vy
    vex
    #
    snss
    sylibr
    #
    @46
    wph
    @66
    @52
    wph
    @60
    vk
    cA
    fsumabs.2
    ralrimiva
    syl
    @60
    @67
    vk
    @29
    cA
    vk
    @47
    cc
    vk
    @29
    cB
    nfcsb1v
    nfel1
    @57
    @29
    wceq
    cB
    @47
    cc
    vk
    @29
    cB
    csbeq1a
    eleq1d
    rspc
    sylc
    #
    abscld
    #
    leadd1d
    @46
    @35
    @51
    @49
    cle
    @46
    @35
    @25
    @30
    @3
    vk
    csu
    #
    caddc
    co
    @51
    @46
    @21
    @30
    @3
    @31
    vk
    @46
    @43
    @21
    @30
    cin
    c0
    wceq
    wph
    @43
    @32
    simplr
    @21
    @29
    disjsn
    sylibr
    #
    @46
    @31
    eqidd
    #
    @46
    @6
    @32
    @31
    cfn
    wcel
    @53
    @54
    cA
    @31
    ssfi
    syl2anc
    #
    @46
    @57
    @31
    wcel
    #
    wa
    #
    @3
    @77
    cB
    @46
    @76
    @59
    @60
    @46
    @31
    cA
    @57
    @54
    sselda
    @61
    syldan
    #
    abscld
    #
    recnd
    fsumsplit
    @46
    @72
    @48
    @25
    caddc
    @46
    @72
    vk
    @29
    @3
    csb
    #
    @48
    @46
    @29
    cvv
    wcel
    #
    @80
    cc
    wcel
    @72
    @80
    wceq
    @68
    @46
    @80
    @48
    cc
    @81
    @80
    @48
    wceq
    @68
    vk
    @29
    cB
    cvv
    cabs
    csbfv2g
    ax-mp
    #
    @46
    @48
    @71
    recnd
    syl5eqel
    @3
    vk
    @29
    cvv
    sumsns
    sylancr
    @82
    syl6eq
    oveq2d
    eqtrd
    breq2d
    bitr4d
    @46
    @34
    @49
    cle
    wbr
    #
    @50
    @36
    @46
    @34
    @23
    @47
    caddc
    co
    #
    cabs
    cfv
    @49
    cle
    @46
    @33
    @84
    cabs
    @46
    @33
    @23
    @30
    cB
    vk
    csu
    #
    caddc
    co
    @84
    @46
    @21
    @30
    cB
    @31
    vk
    @73
    @74
    @75
    @78
    fsumsplit
    @46
    @85
    @47
    @23
    caddc
    @46
    @65
    @67
    @85
    @47
    wceq
    @69
    @70
    cB
    vk
    @29
    cA
    sumsns
    syl2anc
    oveq2d
    eqtrd
    fveq2d
    @46
    @23
    @47
    @63
    @70
    abstrid
    eqbrtrd
    @46
    @34
    cr
    wcel
    @49
    cr
    wcel
    @35
    cr
    wcel
    @83
    @50
    wa
    @36
    wi
    @46
    @33
    @46
    @31
    cB
    vk
    @75
    @78
    fsumcl
    abscld
    @46
    @24
    @48
    @64
    @71
    readdcld
    @46
    @31
    @3
    vk
    @75
    @79
    fsumrecl
    @34
    @49
    @35
    letr
    syl3anc
    mpand
    sylbid
    ex
    a2d
    syl5
    expcom
    a2d
    adantl
    findcard2s
    mpcom
    mpi
end
