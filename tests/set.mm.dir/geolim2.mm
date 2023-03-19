include "caddc.mm"
include "cseq.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "csu.mm"
include "c1.mm"
include "cmin.mm"
include "cdiv.mm"
include "cli.mm"
include "eqid.mm"
include "nn0zd.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "adantr.mm"
include "cn0.mm"
include "eluznn0.mm"
include "sylan.mm"
include "expcld.mm"
include "cmpt.mm"
include "cdm.mm"
include "wceq.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "eqtr4d.mm"
include "seqfeq.mm"
include "cc0.mm"
include "wbr.mm"
include "adantl.mm"
include "geolim.mm"
include "seqex.mm"
include "breldm.mm"
include "nn0uz.mm"
include "expcl.mm"
include "eqeltrd.mm"
include "iserex.mm"
include "mpbid.mm"
include "eqeltrrd.mm"
include "isumclim2.mm"
include "cfz.mm"
include "isumsplit.mm"
include "0zd.mm"
include "isumclim.mm"
include "eqtr3d.mm"
include "cabs.mm"
include "clt.mm"
include "wne.mm"
include "1re.mm"
include "ltnri.mm"
include "fveq2.mm"
include "abs1.mm"
include "syl6eq.mm"
include "breq1d.mm"
include "mtbiri.mm"
include "necon2ai.mm"
include "geoser.mm"
include "oveq1d.mm"
include "1cnd.mm"
include "ax-1cn.mm"
include "subcl.mm"
include "sylancr.mm"
include "necomd.mm"
include "wb.mm"
include "subeq0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "divsubdird.mm"
include "nncan.mm"
include "divcld.mm"
include "isumcl.mm"
include "pncan2d.mm"
include "3eqtr3rd.mm"
include "breqtrd.mm"

theorem geolim2
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cM: class M
  let vj: setvar j
  let vn: setvar n
  assume geolim.1: |- ( ph -> A e. CC )
  assume geolim.2: |- ( ph -> ( abs ` A ) < 1 )
  assume geolim2.3: |- ( ph -> M e. NN0 )
  assume geolim2.4: |- ( ( ph /\ k e. ( ZZ>= ` M ) ) -> ( F ` k ) = ( A ^ k ) )

  disjoint A k
  disjoint F k
  disjoint M k
  disjoint k ph
  disjoint j k
  disjoint j n
  disjoint A j
  disjoint k n
  disjoint A n
  disjoint F j
  disjoint M j
  disjoint j ph
  assert |- ( ph -> seq M ( + , F ) ~~> ( ( A ^ M ) / ( 1 - A ) ) )

  proof
    wph
    caddc
    cF
    cM
    cseq
    #
    cM
    cuz
    cfv
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
    cA
    cM
    cexp
    co
    #
    c1
    cA
    cmin
    co
    #
    cdiv
    co
    #
    cli
    wph
    @3
    vk
    cF
    cM
    @1
    @1
    eqid
    #
    wph
    cM
    geolim2.3
    nn0zd
    #
    geolim2.4
    wph
    @2
    @1
    wcel
    #
    wa
    #
    cA
    @2
    wph
    cA
    cc
    wcel
    #
    @10
    geolim.1
    adantr
    wph
    cM
    cn0
    wcel
    @10
    @2
    cn0
    wcel
    #
    geolim2.3
    @2
    cM
    eluznn0
    sylan
    #
    expcld
    #
    wph
    caddc
    vn
    cn0
    cA
    vn
    cv
    #
    cexp
    co
    #
    cmpt
    #
    cM
    cseq
    #
    @0
    cli
    cdm
    #
    wph
    caddc
    vk
    @18
    cF
    cM
    @9
    @11
    @2
    @18
    cfv
    #
    @3
    @2
    cF
    cfv
    @11
    @13
    @21
    @3
    wceq
    #
    @14
    vn
    @2
    @17
    @3
    cn0
    @18
    @16
    @2
    cA
    cexp
    oveq2
    @18
    eqid
    #
    cA
    @2
    cexp
    ovex
    fvmpt
    #
    syl
    #
    geolim2.4
    eqtr4d
    seqfeq
    wph
    caddc
    @18
    cc0
    cseq
    #
    @20
    wcel
    #
    @19
    @20
    wcel
    wph
    @26
    c1
    @6
    cdiv
    co
    #
    cli
    wbr
    @27
    wph
    cA
    vj
    @18
    geolim.1
    geolim.2
    vj
    cv
    #
    cn0
    wcel
    #
    @29
    @18
    cfv
    #
    cA
    @29
    cexp
    co
    #
    wceq
    wph
    vn
    @29
    @17
    @32
    cn0
    @18
    @16
    @29
    cA
    cexp
    oveq2
    @23
    cA
    @29
    cexp
    ovex
    fvmpt
    adantl
    #
    geolim
    #
    @26
    @28
    cli
    caddc
    @18
    cc0
    seqex
    c1
    @6
    cdiv
    ovex
    breldm
    syl
    #
    wph
    vj
    @18
    cc0
    cM
    cn0
    nn0uz
    geolim2.3
    wph
    @30
    wa
    @31
    @32
    cc
    @33
    wph
    @12
    @30
    @32
    cc
    wcel
    geolim.1
    cA
    @29
    expcl
    sylan
    eqeltrd
    iserex
    mpbid
    #
    eqeltrrd
    isumclim2
    wph
    @28
    c1
    @5
    cmin
    co
    #
    @6
    cdiv
    co
    #
    cmin
    co
    #
    @38
    @4
    caddc
    co
    #
    @38
    cmin
    co
    @7
    @4
    wph
    @28
    @40
    @38
    cmin
    wph
    cc0
    cM
    c1
    cmin
    co
    cfz
    co
    @3
    vk
    csu
    #
    @4
    caddc
    co
    #
    @28
    @40
    wph
    cn0
    @3
    vk
    csu
    @42
    @28
    wph
    @3
    vk
    @18
    cc0
    cM
    @1
    cn0
    nn0uz
    @8
    geolim2.3
    @13
    @22
    wph
    @24
    adantl
    #
    wph
    @12
    @13
    @3
    cc
    wcel
    geolim.1
    cA
    @2
    expcl
    sylan
    #
    @35
    isumsplit
    wph
    @3
    @28
    vk
    @18
    cc0
    cn0
    nn0uz
    wph
    0zd
    @43
    @44
    @34
    isumclim
    eqtr3d
    wph
    @41
    @38
    @4
    caddc
    wph
    cA
    vk
    cM
    geolim.1
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
    geolim.2
    @46
    cA
    c1
    cA
    c1
    wceq
    #
    @46
    c1
    c1
    clt
    wbr
    c1
    1re
    ltnri
    @47
    @45
    c1
    c1
    clt
    @47
    @45
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
    geolim2.3
    geoser
    oveq1d
    eqtr3d
    oveq1d
    wph
    c1
    @37
    cmin
    co
    #
    @6
    cdiv
    co
    @39
    @7
    wph
    c1
    @37
    @6
    wph
    1cnd
    wph
    c1
    cc
    wcel
    #
    @5
    cc
    wcel
    #
    @37
    cc
    wcel
    ax-1cn
    wph
    cA
    cM
    geolim.1
    geolim2.3
    expcld
    #
    c1
    @5
    subcl
    sylancr
    #
    wph
    @50
    @12
    @6
    cc
    wcel
    ax-1cn
    geolim.1
    c1
    cA
    subcl
    sylancr
    #
    wph
    @6
    cc0
    wne
    c1
    cA
    wne
    wph
    cA
    c1
    @48
    necomd
    wph
    @6
    cc0
    c1
    cA
    wph
    @50
    @12
    @6
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
    divsubdird
    wph
    @49
    @5
    @6
    cdiv
    wph
    @50
    @51
    @49
    @5
    wceq
    ax-1cn
    @52
    c1
    @5
    nncan
    sylancr
    oveq1d
    eqtr3d
    wph
    @38
    @4
    wph
    @37
    @6
    @53
    @54
    @55
    divcld
    wph
    @3
    vk
    @18
    cM
    @1
    @8
    @9
    @25
    @15
    @36
    isumcl
    pncan2d
    3eqtr3rd
    breqtrd
end
