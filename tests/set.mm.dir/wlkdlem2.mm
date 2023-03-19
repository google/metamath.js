include "chash.mm"
include "cfv.mm"
include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "wi.mm"
include "cv.mm"
include "cc0.mm"
include "cfzo.mm"
include "wral.mm"
include "caddc.mm"
include "cpr.mm"
include "wss.mm"
include "fzo0end.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "preq12d.mm"
include "sseq12d.mm"
include "rspcv.mm"
include "syl.mm"
include "wa.mm"
include "fvex.mm"
include "prss.mm"
include "cc.mm"
include "nncn.mm"
include "npcan1.mm"
include "eleq1d.mm"
include "biimpd.mm"
include "adantld.mm"
include "syl5bir.mm"
include "syld.mm"
include "syl5com.mm"
include "simpl.mm"
include "sylbir.mm"
include "a1i.mm"
include "ralimdva.mm"
include "mpd.mm"
include "jca.mm"

theorem wlkdlem2
  let wph: wff ph
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cI: class I
  assume wlkd.p: |- ( ph -> P e. Word _V )
  assume wlkd.f: |- ( ph -> F e. Word _V )
  assume wlkd.l: |- ( ph -> ( # ` P ) = ( ( # ` F ) + 1 ) )
  assume wlkd.e: |- ( ph -> A. k e. ( 0 ..^ ( # ` F ) ) { ( P ` k ) , ( P ` ( k + 1 ) ) } C_ ( I ` ( F ` k ) ) )

  disjoint F k
  disjoint P k
  disjoint I k
  disjoint k ph
  assert |- ( ph -> ( ( ( # ` F ) e. NN -> ( P ` ( # ` F ) ) e. ( I ` ( F ` ( ( # ` F ) - 1 ) ) ) ) /\ A. k e. ( 0 ..^ ( # ` F ) ) ( P ` k ) e. ( I ` ( F ` k ) ) ) )

  proof
    wph
    cF
    chash
    cfv
    #
    cn
    wcel
    #
    @0
    cP
    cfv
    #
    @0
    c1
    cmin
    co
    #
    cF
    cfv
    #
    cI
    cfv
    #
    wcel
    #
    wi
    vk
    cv
    #
    cP
    cfv
    #
    @7
    cF
    cfv
    #
    cI
    cfv
    #
    wcel
    #
    vk
    cc0
    @0
    cfzo
    co
    #
    wral
    #
    wph
    @8
    @7
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    @10
    wss
    #
    vk
    @12
    wral
    #
    @1
    @6
    wlkd.e
    @1
    @18
    @3
    cP
    cfv
    #
    @3
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    @5
    wss
    #
    @6
    @1
    @3
    @12
    wcel
    @18
    @23
    wi
    @0
    fzo0end
    @17
    @23
    vk
    @3
    @12
    @7
    @3
    wceq
    #
    @16
    @22
    @10
    @5
    @24
    @8
    @19
    @15
    @21
    @7
    @3
    cP
    fveq2
    @24
    @14
    @20
    cP
    @7
    @3
    c1
    caddc
    oveq1
    fveq2d
    preq12d
    @24
    @9
    @4
    cI
    @7
    @3
    cF
    fveq2
    fveq2d
    sseq12d
    rspcv
    syl
    @23
    @19
    @5
    wcel
    #
    @21
    @5
    wcel
    #
    wa
    @1
    @6
    @19
    @21
    @5
    @3
    cP
    fvex
    @20
    cP
    fvex
    prss
    @1
    @26
    @6
    @25
    @1
    @26
    @6
    @1
    @21
    @2
    @5
    @1
    @20
    @0
    cP
    @1
    @0
    cc
    wcel
    @20
    @0
    wceq
    @0
    nncn
    @0
    npcan1
    syl
    fveq2d
    eleq1d
    biimpd
    adantld
    syl5bir
    syld
    syl5com
    wph
    @18
    @13
    wlkd.e
    wph
    @17
    @11
    vk
    @12
    @17
    @11
    wi
    wph
    @7
    @12
    wcel
    wa
    @17
    @11
    @15
    @10
    wcel
    #
    wa
    @11
    @8
    @15
    @10
    @7
    cP
    fvex
    @14
    cP
    fvex
    prss
    @11
    @27
    simpl
    sylbir
    a1i
    ralimdva
    mpd
    jca
end
