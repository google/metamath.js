include "crli.mm"
include "cdm.mm"
include "wcel.mm"
include "cafv.mm"
include "wbr.mm"
include "cv.mm"
include "wex.mm"
include "eldmg.mm"
include "ibi.mm"
include "wa.mm"
include "simpr.mm"
include "cfv.mm"
include "wdfat.mm"
include "wceq.mm"
include "weu.mm"
include "cvv.mm"
include "rlimrel.mm"
include "brrelexi.mm"
include "adantl.mm"
include "vex.mm"
include "a1i.mm"
include "breldmg.mm"
include "syl3anc.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "breq2.mm"
include "biimprd.mm"
include "spimev.mm"
include "cc.mm"
include "wf.mm"
include "adantr.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cpnf.mm"
include "simprl.mm"
include "simprr.mm"
include "rlimuni.mm"
include "ex.mm"
include "alrimivv.mm"
include "eu4.mm"
include "sylanbrc.mm"
include "dfdfat2.mm"
include "afvfundmfveq.mm"
include "syl.mm"
include "cio.mm"
include "df-fv.mm"
include "wb.mm"
include "expr.mm"
include "syl5ibrcom.mm"
include "impbid.mm"
include "iota5.mm"
include "mpan2.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "exlimdv.mm"
include "syl5.mm"
include "releldmi.mm"
include "impbid1.mm"

theorem rlimdmafv
  let wph: wff ph
  let cA: class A
  let cF: class F
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume rlimdmafv.1: |- ( ph -> F : A --> CC )
  assume rlimdmafv.2: |- ( ph -> sup ( A , RR* , < ) = +oo )


  assert |- ( ph -> ( F e. dom ~~>r <-> F ~~>r ( ~~>r ''' F ) ) )

  proof
    wph
    cF
    crli
    cdm
    #
    wcel
    #
    cF
    cF
    crli
    cafv
    #
    crli
    wbr
    #
    @1
    cF
    vx
    cv
    #
    crli
    wbr
    #
    vx
    wex
    #
    wph
    @3
    @1
    @6
    vx
    cF
    crli
    @0
    eldmg
    ibi
    wph
    @5
    @3
    vx
    wph
    @5
    @3
    wph
    @5
    wa
    #
    cF
    @4
    @2
    crli
    wph
    @5
    simpr
    #
    @7
    @2
    cF
    crli
    cfv
    #
    @4
    @7
    cF
    crli
    wdfat
    #
    @2
    @9
    wceq
    @7
    @1
    cF
    vy
    cv
    #
    crli
    wbr
    #
    vy
    weu
    #
    @10
    @7
    cF
    cvv
    wcel
    #
    @4
    cvv
    wcel
    #
    @5
    @1
    @5
    @14
    wph
    cF
    @4
    crli
    rlimrel
    brrelexi
    adantl
    @15
    @7
    vx
    vex
    #
    a1i
    @8
    cF
    @4
    cvv
    cvv
    crli
    breldmg
    syl3anc
    @7
    @12
    vy
    wex
    #
    @12
    cF
    vz
    cv
    #
    crli
    wbr
    #
    wa
    #
    vy
    vz
    weq
    #
    wi
    #
    vz
    wal
    vy
    wal
    @13
    @5
    @17
    wph
    @5
    @12
    vy
    vx
    vy
    vx
    weq
    @12
    @5
    @11
    @4
    cF
    crli
    breq2
    biimprd
    spimev
    adantl
    @7
    @22
    vy
    vz
    @7
    @20
    @21
    @7
    @20
    wa
    cA
    @11
    @18
    cF
    @7
    cA
    cc
    cF
    wf
    #
    @20
    wph
    @23
    @5
    rlimdmafv.1
    adantr
    adantr
    @7
    cA
    cxr
    clt
    csup
    cpnf
    wceq
    #
    @20
    wph
    @24
    @5
    rlimdmafv.2
    adantr
    adantr
    @7
    @12
    @19
    simprl
    @7
    @12
    @19
    simprr
    rlimuni
    ex
    alrimivv
    @12
    @19
    vy
    vz
    @11
    @18
    cF
    crli
    breq2
    eu4
    sylanbrc
    vy
    cF
    crli
    dfdfat2
    sylanbrc
    cF
    crli
    afvfundmfveq
    syl
    @7
    @9
    cF
    vw
    cv
    #
    crli
    wbr
    #
    vw
    cio
    #
    @4
    vw
    cF
    crli
    df-fv
    @7
    @15
    @27
    @4
    wceq
    @16
    @7
    @26
    vw
    @4
    cvv
    @7
    @26
    vw
    vx
    weq
    #
    wb
    @15
    @7
    @26
    @28
    wph
    @5
    @26
    @28
    wph
    @5
    @26
    wa
    #
    wa
    cA
    @25
    @4
    cF
    wph
    @23
    @29
    rlimdmafv.1
    adantr
    wph
    @24
    @29
    rlimdmafv.2
    adantr
    wph
    @5
    @26
    simprr
    wph
    @5
    @26
    simprl
    rlimuni
    expr
    @7
    @26
    @28
    @5
    @8
    @25
    @4
    cF
    crli
    breq2
    syl5ibrcom
    impbid
    adantr
    iota5
    mpan2
    syl5eq
    eqtrd
    breqtrrd
    ex
    exlimdv
    syl5
    cF
    @2
    crli
    rlimrel
    releldmi
    impbid1
end
