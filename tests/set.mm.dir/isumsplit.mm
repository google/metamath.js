include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "csu.mm"
include "caddc.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "syl6eleq.mm"
include "eluzel2.mm"
include "syl.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "eluzelz.mm"
include "cv.mm"
include "wceq.mm"
include "wss.mm"
include "uzss.mm"
include "3sstr4g.mm"
include "sselda.mm"
include "syldan.mm"
include "cc.mm"
include "wa.mm"
include "eqeltrd.mm"
include "iserex.mm"
include "mpbid.mm"
include "isumclim2.mm"
include "fzfid.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "sylan2.mm"
include "fsumcl.mm"
include "serf.mm"
include "ffvelrnda.mm"
include "cc0.mm"
include "c0.mm"
include "clt.mm"
include "wbr.mm"
include "zred.mm"
include "ltm1d.mm"
include "wb.mm"
include "peano2zm.mm"
include "fzn.mm"
include "syl2anc.mm"
include "sumeq1d.mm"
include "adantr.mm"
include "sum0.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "addid2d.mm"
include "eqtr2d.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "seqeq1.mm"
include "fveq1d.mm"
include "oveq12d.mm"
include "eqeq2d.mm"
include "syl5ibrcom.mm"
include "addcl.mm"
include "adantl.mm"
include "w3a.mm"
include "addass.mm"
include "simplr.mm"
include "simpll.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "eleqtrd.mm"
include "eluzp1m1.mm"
include "sylan.mm"
include "syl2an.mm"
include "seqsplit.mm"
include "fsumser.mm"
include "seqeq1d.mm"
include "eqtr4d.mm"
include "ex.mm"
include "wo.mm"
include "uzp1.mm"
include "mpjaod.mm"
include "climaddc2.mm"
include "isumclim.mm"

theorem isumsplit
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let cW: class W
  let cZ: class Z
  let vj: setvar j
  let vm: setvar m
  let vx: setvar x
  assume isumsplit.1: |- Z = ( ZZ>= ` M )
  assume isumsplit.2: |- W = ( ZZ>= ` N )
  assume isumsplit.3: |- ( ph -> N e. Z )
  assume isumsplit.4: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = A )
  assume isumsplit.5: |- ( ( ph /\ k e. Z ) -> A e. CC )
  assume isumsplit.6: |- ( ph -> seq M ( + , F ) e. dom ~~> )

  disjoint F k
  disjoint M k
  disjoint k ph
  disjoint Z k
  disjoint N k
  disjoint W k
  disjoint A j
  disjoint j k
  disjoint j m
  disjoint j x
  disjoint F j
  disjoint k m
  disjoint k x
  disjoint m x
  disjoint F m
  disjoint F x
  disjoint M j
  disjoint M m
  disjoint M x
  disjoint j ph
  disjoint m ph
  disjoint ph x
  disjoint N j
  disjoint N m
  disjoint N x
  disjoint W j
  disjoint W m
  disjoint W x
  assert |- ( ph -> sum_ k e. Z A = ( sum_ k e. ( M ... ( N - 1 ) ) A + sum_ k e. W A ) )

  proof
    wph
    cA
    cM
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    cA
    vk
    csu
    #
    cW
    cA
    vk
    csu
    #
    caddc
    co
    vk
    cF
    cM
    cZ
    isumsplit.1
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    cM
    cz
    wcel
    #
    wph
    cN
    cZ
    @4
    isumsplit.3
    isumsplit.1
    syl6eleq
    #
    cM
    cN
    eluzel2
    syl
    #
    isumsplit.4
    isumsplit.5
    wph
    @3
    @2
    vj
    caddc
    cF
    cN
    cseq
    #
    caddc
    cF
    cM
    cseq
    #
    cN
    cli
    cdm
    #
    cW
    isumsplit.2
    wph
    @5
    cN
    cz
    wcel
    @7
    cM
    cN
    eluzelz
    syl
    #
    wph
    cA
    vk
    cF
    cN
    cW
    isumsplit.2
    @12
    wph
    vk
    cv
    #
    cW
    wcel
    #
    @13
    cZ
    wcel
    #
    @13
    cF
    cfv
    #
    cA
    wceq
    #
    wph
    cW
    cZ
    @13
    wph
    cN
    cuz
    cfv
    #
    @4
    cW
    cZ
    wph
    @5
    @18
    @4
    wss
    @7
    cM
    cN
    uzss
    syl
    isumsplit.2
    isumsplit.1
    3sstr4g
    #
    sselda
    #
    isumsplit.4
    syldan
    wph
    @14
    @15
    cA
    cc
    wcel
    #
    @20
    isumsplit.5
    syldan
    wph
    @10
    @11
    wcel
    @9
    @11
    wcel
    isumsplit.6
    wph
    vk
    cF
    cM
    cN
    cZ
    isumsplit.1
    isumsplit.3
    wph
    @15
    wa
    @16
    cA
    cc
    isumsplit.4
    isumsplit.5
    eqeltrd
    #
    iserex
    mpbid
    isumclim2
    wph
    @1
    cA
    vk
    wph
    cM
    @0
    fzfid
    @13
    @1
    wcel
    #
    wph
    @15
    @21
    @23
    @13
    @4
    cZ
    @13
    cM
    @0
    elfzuz
    isumsplit.1
    syl6eleqr
    #
    isumsplit.5
    sylan2
    fsumcl
    isumsplit.6
    wph
    cW
    cc
    vj
    cv
    #
    @9
    wph
    vk
    cF
    cN
    cW
    isumsplit.2
    @12
    wph
    @14
    @15
    @16
    cc
    wcel
    #
    @20
    @22
    syldan
    serf
    ffvelrnda
    wph
    @25
    cW
    wcel
    #
    wa
    #
    cN
    cM
    wceq
    #
    @25
    @10
    cfv
    #
    @2
    @25
    @9
    cfv
    #
    caddc
    co
    #
    wceq
    #
    cN
    cM
    c1
    caddc
    co
    cuz
    cfv
    wcel
    #
    @28
    @33
    @29
    @30
    cM
    cM
    c1
    cmin
    co
    #
    cfz
    co
    #
    cA
    vk
    csu
    #
    @30
    caddc
    co
    #
    wceq
    @28
    @38
    cc0
    @30
    caddc
    co
    @30
    @28
    @37
    cc0
    @30
    caddc
    @28
    @37
    c0
    cA
    vk
    csu
    #
    cc0
    wph
    @37
    @39
    wceq
    @27
    wph
    @36
    c0
    cA
    vk
    wph
    @35
    cM
    clt
    wbr
    #
    @36
    c0
    wceq
    #
    wph
    cM
    wph
    cM
    @8
    zred
    ltm1d
    wph
    @6
    @35
    cz
    wcel
    #
    @40
    @41
    wb
    @8
    wph
    @6
    @42
    @8
    cM
    peano2zm
    syl
    cM
    @35
    fzn
    syl2anc
    mpbid
    sumeq1d
    adantr
    cA
    vk
    sum0
    syl6eq
    oveq1d
    @28
    @30
    wph
    @27
    @25
    cZ
    wcel
    @30
    cc
    wcel
    wph
    cW
    cZ
    @25
    @19
    sselda
    wph
    cZ
    cc
    @25
    @10
    wph
    vk
    cF
    cM
    cZ
    isumsplit.1
    @8
    @22
    serf
    ffvelrnda
    syldan
    addid2d
    eqtr2d
    @29
    @32
    @38
    @30
    @29
    @2
    @37
    @31
    @30
    caddc
    @29
    @1
    @36
    cA
    vk
    @29
    @0
    @35
    cM
    cfz
    cN
    cM
    c1
    cmin
    oveq1
    oveq2d
    sumeq1d
    @29
    @25
    @9
    @10
    caddc
    cF
    cN
    cM
    seqeq1
    fveq1d
    oveq12d
    eqeq2d
    syl5ibrcom
    @28
    @34
    @33
    @28
    @34
    wa
    #
    @30
    @0
    @10
    cfv
    #
    @25
    caddc
    cF
    @0
    c1
    caddc
    co
    #
    cseq
    #
    cfv
    #
    caddc
    co
    @32
    @43
    vk
    vm
    vx
    caddc
    cc
    cF
    cM
    @0
    @25
    @13
    cc
    wcel
    #
    vm
    cv
    #
    cc
    wcel
    #
    wa
    @13
    @49
    caddc
    co
    #
    cc
    wcel
    @43
    @13
    @49
    addcl
    adantl
    @48
    @50
    vx
    cv
    #
    cc
    wcel
    w3a
    @51
    @52
    caddc
    co
    @13
    @49
    @52
    caddc
    co
    caddc
    co
    wceq
    @43
    @13
    @49
    @52
    addass
    adantl
    @43
    @25
    cW
    @45
    cuz
    cfv
    #
    wph
    @27
    @34
    simplr
    @43
    cW
    @18
    @53
    isumsplit.2
    @43
    cN
    @45
    cuz
    @43
    wph
    cN
    @45
    wceq
    wph
    @27
    @34
    simpll
    #
    wph
    @45
    cN
    wph
    cN
    cc
    wcel
    c1
    cc
    wcel
    @45
    cN
    wceq
    wph
    cN
    @12
    zcnd
    ax-1cn
    cN
    c1
    npcan
    sylancl
    eqcomd
    syl
    #
    fveq2d
    syl5eq
    eleqtrd
    @28
    @6
    @34
    @0
    @4
    wcel
    wph
    @6
    @27
    @8
    adantr
    cM
    cN
    eluzp1m1
    sylan
    #
    @43
    wph
    @15
    @26
    @13
    cM
    @25
    cfz
    co
    wcel
    #
    @54
    @57
    @13
    @4
    cZ
    @13
    cM
    @25
    elfzuz
    isumsplit.1
    syl6eleqr
    @22
    syl2an
    seqsplit
    @43
    @2
    @44
    @31
    @47
    caddc
    @43
    cA
    vk
    cF
    cM
    @0
    @43
    wph
    @15
    @17
    @23
    @54
    @24
    isumsplit.4
    syl2an
    @56
    @43
    wph
    @15
    @21
    @23
    @54
    @24
    isumsplit.5
    syl2an
    fsumser
    @43
    @25
    @9
    @46
    @43
    cN
    @45
    caddc
    cF
    @55
    seqeq1d
    fveq1d
    oveq12d
    eqtr4d
    ex
    wph
    @29
    @34
    wo
    #
    @27
    wph
    @5
    @58
    @7
    cM
    cN
    uzp1
    syl
    adantr
    mpjaod
    climaddc2
    isumclim
end
