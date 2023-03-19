include "cv.mm"
include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "cdm.mm"
include "wcel.mm"
include "wceq.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "wo.mm"
include "uzm1.mm"
include "eleq2s.mm"
include "ad2antlr.mm"
include "wi.mm"
include "seqeq1.mm"
include "breq1d.mm"
include "seqex.mm"
include "vex.mm"
include "breldm.mm"
include "syl6bi.mm"
include "adantld.mm"
include "simplr.mm"
include "cc.mm"
include "adantlr.mm"
include "caddc.mm"
include "cz.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "zcnd.mm"
include "1cnd.mm"
include "npcand.mm"
include "seqeq1d.mm"
include "biimpar.mm"
include "clim2prod.mm"
include "ovex.mm"
include "syl.mm"
include "an32s.mm"
include "expcom.mm"
include "eqcomi.mm"
include "jaoi.mm"
include "mpcom.mm"
include "ex.mm"
include "exlimdv.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem ntrivcvg
  let wph: wff ph
  let vy: setvar y
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cZ: class Z
  assume ntrivcvg.1: |- Z = ( ZZ>= ` M )
  assume ntrivcvg.2: |- ( ph -> E. n e. Z E. y ( y =/= 0 /\ seq n ( x. , F ) ~~> y ) )
  assume ntrivcvg.3: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )

  disjoint F k
  disjoint F n
  disjoint F y
  disjoint k n
  disjoint k ph
  disjoint k y
  disjoint M k
  disjoint M n
  disjoint M y
  disjoint n ph
  disjoint n y
  disjoint ph y
  disjoint Z k
  disjoint Z y
  assert |- ( ph -> seq M ( x. , F ) e. dom ~~> )

  proof
    wph
    vy
    cv
    #
    cc0
    wne
    #
    cmul
    cF
    vn
    cv
    #
    cseq
    #
    @0
    cli
    wbr
    #
    wa
    #
    vy
    wex
    #
    vn
    cZ
    wrex
    cmul
    cF
    cM
    cseq
    #
    cli
    cdm
    wcel
    #
    ntrivcvg.2
    wph
    @6
    @8
    vn
    cZ
    wph
    @2
    cZ
    wcel
    #
    wa
    #
    @5
    @8
    vy
    @10
    @4
    @8
    @1
    @10
    @4
    @8
    @2
    cM
    wceq
    #
    @2
    c1
    cmin
    co
    #
    cM
    cuz
    cfv
    #
    wcel
    #
    wo
    #
    @10
    @4
    wa
    #
    @8
    @9
    @15
    wph
    @4
    @15
    @2
    @13
    cZ
    cM
    @2
    uzm1
    ntrivcvg.1
    eleq2s
    ad2antlr
    @11
    @16
    @8
    wi
    #
    @14
    @11
    @4
    @8
    @10
    @11
    @4
    @7
    @0
    cli
    wbr
    @8
    @11
    @3
    @7
    @0
    cli
    cmul
    cF
    @2
    cM
    seqeq1
    breq1d
    @7
    @0
    cli
    cmul
    cF
    cM
    seqex
    #
    vy
    vex
    breldm
    syl6bi
    adantld
    @17
    @12
    cZ
    @13
    @16
    @12
    cZ
    wcel
    #
    @8
    @10
    @19
    @4
    @8
    @10
    @19
    wa
    #
    @4
    wa
    #
    @7
    @12
    @7
    cfv
    #
    @0
    cmul
    co
    #
    cli
    wbr
    @8
    @21
    @0
    vk
    cF
    cM
    @12
    cZ
    ntrivcvg.1
    @10
    @19
    @4
    simplr
    @20
    vk
    cv
    #
    cZ
    wcel
    #
    @24
    cF
    cfv
    cc
    wcel
    #
    @4
    @10
    @25
    @26
    @19
    wph
    @25
    @26
    @9
    ntrivcvg.3
    adantlr
    adantlr
    adantlr
    @20
    cmul
    cF
    @12
    c1
    caddc
    co
    #
    cseq
    #
    @0
    cli
    wbr
    @4
    @20
    @28
    @3
    @0
    cli
    @20
    @27
    @2
    cmul
    cF
    @20
    @2
    c1
    @20
    @2
    @20
    cZ
    cz
    @2
    cZ
    @13
    cz
    ntrivcvg.1
    cM
    uzssz
    eqsstri
    wph
    @9
    @19
    simplr
    sseldi
    zcnd
    @20
    1cnd
    npcand
    seqeq1d
    breq1d
    biimpar
    clim2prod
    @7
    @23
    cli
    @18
    @22
    @0
    cmul
    ovex
    breldm
    syl
    an32s
    expcom
    cZ
    @13
    ntrivcvg.1
    eqcomi
    eleq2s
    jaoi
    mpcom
    ex
    adantld
    exlimdv
    rexlimdva
    mpd
end
