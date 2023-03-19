include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "wss.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "wral.mm"
include "wne.mm"
include "wceq.mm"
include "csn.mm"
include "wif.mm"
include "wa.mm"
include "r19.26.mm"
include "wn.mm"
include "wb.mm"
include "df-ne.mm"
include "ifpfal.mm"
include "sylbi.mm"
include "biimparc.mm"
include "ralimi.mm"
include "sylbir.mm"
include "syl2anc.mm"

theorem wlkdlem4
  let wph: wff ph
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cI: class I
  assume wlkd.p: |- ( ph -> P e. Word _V )
  assume wlkd.f: |- ( ph -> F e. Word _V )
  assume wlkd.l: |- ( ph -> ( # ` P ) = ( ( # ` F ) + 1 ) )
  assume wlkd.e: |- ( ph -> A. k e. ( 0 ..^ ( # ` F ) ) { ( P ` k ) , ( P ` ( k + 1 ) ) } C_ ( I ` ( F ` k ) ) )
  assume wlkd.n: |- ( ph -> A. k e. ( 0 ..^ ( # ` F ) ) ( P ` k ) =/= ( P ` ( k + 1 ) ) )

  disjoint F k
  disjoint P k
  disjoint I k
  disjoint k ph
  assert |- ( ph -> A. k e. ( 0 ..^ ( # ` F ) ) if- ( ( P ` k ) = ( P ` ( k + 1 ) ) , ( I ` ( F ` k ) ) = { ( P ` k ) } , { ( P ` k ) , ( P ` ( k + 1 ) ) } C_ ( I ` ( F ` k ) ) ) )

  proof
    wph
    vk
    cv
    #
    cP
    cfv
    #
    @0
    c1
    caddc
    co
    cP
    cfv
    #
    cpr
    @0
    cF
    cfv
    cI
    cfv
    #
    wss
    #
    vk
    cc0
    cF
    chash
    cfv
    cfzo
    co
    #
    wral
    #
    @1
    @2
    wne
    #
    vk
    @5
    wral
    #
    @1
    @2
    wceq
    #
    @3
    @1
    csn
    wceq
    #
    @4
    wif
    #
    vk
    @5
    wral
    #
    wlkd.e
    wlkd.n
    @6
    @8
    wa
    @4
    @7
    wa
    #
    vk
    @5
    wral
    @12
    @4
    @7
    vk
    @5
    r19.26
    @13
    @11
    vk
    @5
    @7
    @11
    @4
    @7
    @9
    wn
    @11
    @4
    wb
    @1
    @2
    df-ne
    @9
    @10
    @4
    ifpfal
    sylbi
    biimparc
    ralimi
    sylbir
    syl2anc
end
