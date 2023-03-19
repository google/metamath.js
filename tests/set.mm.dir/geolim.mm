include "caddc.mm"
include "cc0.mm"
include "cseq.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "cli.mm"
include "cn0.mm"
include "cv.mm"
include "cexp.mm"
include "cmpt.mm"
include "cvv.mm"
include "nn0uz.mm"
include "0zd.mm"
include "cmul.mm"
include "expcnv.mm"
include "cc.mm"
include "wcel.mm"
include "ax-1cn.mm"
include "subcl.mm"
include "sylancr.mm"
include "wne.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "1re.mm"
include "ltnri.mm"
include "fveq2.mm"
include "abs1.mm"
include "syl6eq.mm"
include "breq1d.mm"
include "mtbiri.mm"
include "necon2ai.mm"
include "syl.mm"
include "necomd.mm"
include "wb.mm"
include "subeq0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "divcld.mm"
include "nn0ex.mm"
include "mptex.mm"
include "a1i.mm"
include "wa.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "expcl.mm"
include "sylan.mm"
include "eqeltrd.mm"
include "expp1.mm"
include "adantr.mm"
include "mulcomd.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "div23d.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "climmulc2.mm"
include "mul01d.mm"
include "breqtrd.mm"
include "reccld.mm"
include "seqex.mm"
include "peano2nn0.mm"
include "syl2an.mm"
include "cfz.mm"
include "csu.mm"
include "nn0cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "sumeq1d.mm"
include "divsubdird.mm"
include "geoser.mm"
include "simpll.mm"
include "elfznn0.mm"
include "syl2anc.mm"
include "cuz.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "expcld.mm"
include "fsumser.mm"
include "3eqtr3rd.mm"
include "climsubc2.mm"
include "subid1d.mm"

theorem geolim
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let vj: setvar j
  let vn: setvar n
  let cM: class M
  assume geolim.1: |- ( ph -> A e. CC )
  assume geolim.2: |- ( ph -> ( abs ` A ) < 1 )
  assume geolim.3: |- ( ( ph /\ k e. NN0 ) -> ( F ` k ) = ( A ^ k ) )

  disjoint A k
  disjoint F k
  disjoint k ph
  disjoint j k
  disjoint j n
  disjoint A j
  disjoint k n
  disjoint A n
  disjoint F j
  disjoint M j
  disjoint M k
  disjoint j ph
  assert |- ( ph -> seq 0 ( + , F ) ~~> ( 1 / ( 1 - A ) ) )

  proof
    wph
    caddc
    cF
    cc0
    cseq
    #
    c1
    c1
    cA
    cmin
    co
    #
    cdiv
    co
    #
    cc0
    cmin
    co
    @2
    cli
    wph
    cc0
    @2
    vj
    vn
    cn0
    cA
    vn
    cv
    #
    c1
    caddc
    co
    #
    cexp
    co
    #
    @1
    cdiv
    co
    #
    cmpt
    #
    @0
    cc0
    cvv
    cn0
    nn0uz
    wph
    0zd
    #
    wph
    @7
    cA
    @1
    cdiv
    co
    #
    cc0
    cmul
    co
    cc0
    cli
    wph
    cc0
    @9
    vj
    vn
    cn0
    cA
    @3
    cexp
    co
    #
    cmpt
    #
    @7
    cc0
    cvv
    cn0
    nn0uz
    @8
    wph
    cA
    vn
    geolim.1
    geolim.2
    expcnv
    wph
    cA
    @1
    geolim.1
    wph
    c1
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    @1
    cc
    wcel
    #
    ax-1cn
    geolim.1
    c1
    cA
    subcl
    sylancr
    #
    wph
    @1
    cc0
    wne
    #
    c1
    cA
    wne
    wph
    cA
    c1
    wph
    cA
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    cA
    c1
    wne
    #
    geolim.2
    @18
    cA
    c1
    cA
    c1
    wceq
    #
    @18
    c1
    c1
    clt
    wbr
    c1
    1re
    ltnri
    @20
    @17
    c1
    c1
    clt
    @20
    @17
    c1
    cabs
    cfv
    c1
    cA
    c1
    cabs
    fveq2
    abs1
    syl6eq
    breq1d
    mtbiri
    necon2ai
    syl
    #
    necomd
    wph
    @1
    cc0
    c1
    cA
    wph
    @12
    @13
    @1
    cc0
    wceq
    c1
    cA
    wceq
    wb
    ax-1cn
    geolim.1
    c1
    cA
    subeq0
    sylancr
    necon3bid
    mpbird
    #
    divcld
    #
    @7
    cvv
    wcel
    wph
    vn
    cn0
    @6
    nn0ex
    mptex
    a1i
    wph
    vj
    cv
    #
    cn0
    wcel
    #
    wa
    #
    @24
    @11
    cfv
    #
    cA
    @24
    cexp
    co
    #
    cc
    @25
    @27
    @28
    wceq
    wph
    vn
    @24
    @10
    @28
    cn0
    @11
    @3
    @24
    cA
    cexp
    oveq2
    @11
    eqid
    cA
    @24
    cexp
    ovex
    fvmpt
    adantl
    #
    wph
    @13
    @25
    @28
    cc
    wcel
    geolim.1
    cA
    @24
    expcl
    sylan
    #
    eqeltrd
    @26
    cA
    @24
    c1
    caddc
    co
    #
    cexp
    co
    #
    @1
    cdiv
    co
    #
    @9
    @28
    cmul
    co
    #
    @24
    @7
    cfv
    #
    @9
    @27
    cmul
    co
    @26
    @33
    cA
    @28
    cmul
    co
    #
    @1
    cdiv
    co
    @34
    @26
    @32
    @36
    @1
    cdiv
    @26
    @32
    @28
    cA
    cmul
    co
    #
    @36
    wph
    @13
    @25
    @32
    @37
    wceq
    geolim.1
    cA
    @24
    expp1
    sylan
    @26
    @28
    cA
    @30
    wph
    @13
    @25
    geolim.1
    adantr
    #
    mulcomd
    eqtrd
    oveq1d
    @26
    cA
    @28
    @1
    @38
    @30
    wph
    @14
    @25
    @15
    adantr
    #
    wph
    @16
    @25
    @22
    adantr
    #
    div23d
    eqtrd
    @25
    @35
    @33
    wceq
    wph
    vn
    @24
    @6
    @33
    cn0
    @7
    @3
    @24
    wceq
    #
    @5
    @32
    @1
    cdiv
    @41
    @4
    @31
    cA
    cexp
    @3
    @24
    c1
    caddc
    oveq1
    oveq2d
    oveq1d
    @7
    eqid
    @32
    @1
    cdiv
    ovex
    fvmpt
    adantl
    #
    @26
    @27
    @28
    @9
    cmul
    @29
    oveq2d
    3eqtr4d
    climmulc2
    wph
    @9
    @23
    mul01d
    breqtrd
    wph
    @1
    @15
    @22
    reccld
    #
    @0
    cvv
    wcel
    wph
    caddc
    cF
    cc0
    seqex
    a1i
    @26
    @35
    @33
    cc
    @42
    @26
    @32
    @1
    wph
    @13
    @31
    cn0
    wcel
    #
    @32
    cc
    wcel
    @25
    geolim.1
    @24
    peano2nn0
    #
    cA
    @31
    expcl
    syl2an
    #
    @39
    @40
    divcld
    eqeltrd
    @26
    cc0
    @31
    c1
    cmin
    co
    #
    cfz
    co
    #
    cA
    vk
    cv
    #
    cexp
    co
    #
    vk
    csu
    #
    cc0
    @24
    cfz
    co
    #
    @50
    vk
    csu
    @2
    @35
    cmin
    co
    #
    @24
    @0
    cfv
    @26
    @48
    @52
    @50
    vk
    @26
    @47
    @24
    cc0
    cfz
    @26
    @24
    cc
    wcel
    #
    @12
    @47
    @24
    wceq
    @25
    @54
    wph
    @24
    nn0cn
    adantl
    ax-1cn
    @24
    c1
    pncan
    sylancl
    oveq2d
    sumeq1d
    @26
    c1
    @32
    cmin
    co
    @1
    cdiv
    co
    @2
    @33
    cmin
    co
    @51
    @53
    @26
    c1
    @32
    @1
    @12
    @26
    ax-1cn
    a1i
    @46
    @39
    @40
    divsubdird
    @26
    cA
    vk
    @31
    @38
    wph
    @19
    @25
    @21
    adantr
    @25
    @44
    wph
    @45
    adantl
    geoser
    @26
    @35
    @33
    @2
    cmin
    @42
    oveq2d
    3eqtr4d
    @26
    @50
    vk
    cF
    cc0
    @24
    @26
    @49
    @52
    wcel
    #
    wa
    #
    wph
    @49
    cn0
    wcel
    #
    @49
    cF
    cfv
    @50
    wceq
    wph
    @25
    @55
    simpll
    #
    @55
    @57
    @26
    @49
    @24
    elfznn0
    adantl
    #
    geolim.3
    syl2anc
    @26
    @24
    cn0
    cc0
    cuz
    cfv
    wph
    @25
    simpr
    nn0uz
    syl6eleq
    @56
    cA
    @49
    @56
    wph
    @13
    @58
    geolim.1
    syl
    @59
    expcld
    fsumser
    3eqtr3rd
    climsubc2
    wph
    @2
    @43
    subid1d
    breqtrd
end
