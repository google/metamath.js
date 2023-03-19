include "csu.mm"
include "cdvds.mm"
include "wbr.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "cz.mm"
include "wcel.mm"
include "0z.mm"
include "dvds0.mm"
include "mp1i.mm"
include "simpr.mm"
include "cv.mm"
include "simplr.mm"
include "adantlr.mm"
include "eqbrtrrd.mm"
include "wb.mm"
include "0dvds.mm"
include "syl.mm"
include "mpbid.mm"
include "sumeq2dv.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "cfn.mm"
include "wo.mm"
include "adantr.mm"
include "olcd.mm"
include "sumz.mm"
include "eqtrd.mm"
include "3brtr4d.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "zcnd.mm"
include "fsumdivc.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "fsumzcl.mm"
include "eqeltrd.mm"
include "mpbird.mm"
include "pm2.61dane.mm"

theorem fsumdvds
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cN: class N
  assume fsumdvds.1: |- ( ph -> A e. Fin )
  assume fsumdvds.2: |- ( ph -> N e. ZZ )
  assume fsumdvds.3: |- ( ( ph /\ k e. A ) -> B e. ZZ )
  assume fsumdvds.4: |- ( ( ph /\ k e. A ) -> N || B )

  disjoint A k
  disjoint N k
  disjoint k ph
  assert |- ( ph -> N || sum_ k e. A B )

  proof
    wph
    cN
    cA
    cB
    vk
    csu
    #
    cdvds
    wbr
    #
    cN
    cc0
    wph
    cN
    cc0
    wceq
    #
    wa
    #
    cc0
    cc0
    cN
    @0
    cdvds
    cc0
    cz
    wcel
    cc0
    cc0
    cdvds
    wbr
    @3
    0z
    cc0
    dvds0
    mp1i
    wph
    @2
    simpr
    @3
    @0
    cA
    cc0
    vk
    csu
    #
    cc0
    @3
    cA
    cB
    cc0
    vk
    @3
    vk
    cv
    cA
    wcel
    #
    wa
    #
    cc0
    cB
    cdvds
    wbr
    #
    cB
    cc0
    wceq
    #
    @6
    cN
    cc0
    cB
    cdvds
    wph
    @2
    @5
    simplr
    wph
    @5
    cN
    cB
    cdvds
    wbr
    #
    @2
    fsumdvds.4
    adantlr
    eqbrtrrd
    @6
    cB
    cz
    wcel
    #
    @7
    @8
    wb
    wph
    @5
    @10
    @2
    fsumdvds.3
    adantlr
    cB
    0dvds
    syl
    mpbid
    sumeq2dv
    @3
    cA
    cc0
    cuz
    cfv
    wss
    #
    cA
    cfn
    wcel
    #
    wo
    @4
    cc0
    wceq
    @3
    @12
    @11
    wph
    @12
    @2
    fsumdvds.1
    adantr
    olcd
    cA
    vk
    cc0
    sumz
    syl
    eqtrd
    3brtr4d
    wph
    cN
    cc0
    wne
    #
    wa
    #
    @1
    @0
    cN
    cdiv
    co
    #
    cz
    wcel
    #
    @14
    @15
    cA
    cB
    cN
    cdiv
    co
    #
    vk
    csu
    cz
    @14
    cA
    cB
    cN
    vk
    wph
    @12
    @13
    fsumdvds.1
    adantr
    #
    @14
    cN
    wph
    cN
    cz
    wcel
    #
    @13
    fsumdvds.2
    adantr
    #
    zcnd
    @14
    @5
    wa
    #
    cB
    wph
    @5
    @10
    @13
    fsumdvds.3
    adantlr
    #
    zcnd
    wph
    @13
    simpr
    #
    fsumdivc
    @14
    cA
    @17
    vk
    @18
    @21
    @9
    @17
    cz
    wcel
    #
    wph
    @5
    @9
    @13
    fsumdvds.4
    adantlr
    @21
    @19
    @13
    @10
    @9
    @24
    wb
    @14
    @19
    @5
    @20
    adantr
    wph
    @13
    @5
    simplr
    @22
    cN
    cB
    dvdsval2
    syl3anc
    mpbid
    fsumzcl
    eqeltrd
    @14
    @19
    @13
    @0
    cz
    wcel
    #
    @1
    @16
    wb
    @20
    @23
    wph
    @25
    @13
    wph
    cA
    cB
    vk
    fsumdvds.1
    fsumdvds.3
    fsumzcl
    adantr
    cN
    @0
    dvdsval2
    syl3anc
    mpbird
    pm2.61dane
end
