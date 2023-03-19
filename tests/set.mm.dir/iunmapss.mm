include "cmap.mm"
include "co.mm"
include "ciun.mm"
include "wss.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "ex.mm"
include "ralrimi.mm"
include "iunexg.mm"
include "syl2anc.mm"
include "adantr.mm"
include "ssiun2.mm"
include "adantl.mm"
include "mapss.mm"
include "nfiu1.mm"
include "nfcv.mm"
include "nfov.mm"
include "iunssf.mm"
include "sylibr.mm"

theorem iunmapss
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  assume iunmapss.x: |- F/ x ph
  assume iunmapss.a: |- ( ph -> A e. V )
  assume iunmapss.b: |- ( ( ph /\ x e. A ) -> B e. W )

  disjoint A x
  disjoint C x
  assert |- ( ph -> U_ x e. A ( B ^m C ) C_ ( U_ x e. A B ^m C ) )

  proof
    wph
    cB
    cC
    cmap
    co
    #
    vx
    cA
    cB
    ciun
    #
    cC
    cmap
    co
    #
    wss
    #
    vx
    cA
    wral
    vx
    cA
    @0
    ciun
    @2
    wss
    wph
    @3
    vx
    cA
    iunmapss.x
    wph
    vx
    cv
    cA
    wcel
    #
    @3
    wph
    @4
    wa
    @1
    cvv
    wcel
    #
    cB
    @1
    wss
    #
    @3
    wph
    @5
    @4
    wph
    cA
    cV
    wcel
    cB
    cW
    wcel
    #
    vx
    cA
    wral
    @5
    iunmapss.a
    wph
    @7
    vx
    cA
    iunmapss.x
    wph
    @4
    @7
    iunmapss.b
    ex
    ralrimi
    vx
    cA
    cB
    cV
    cW
    iunexg
    syl2anc
    adantr
    @4
    @6
    wph
    vx
    cA
    cB
    ssiun2
    adantl
    cB
    @1
    cC
    cvv
    mapss
    syl2anc
    ex
    ralrimi
    vx
    cA
    @0
    @2
    vx
    @1
    cC
    cmap
    vx
    cA
    cB
    nfiu1
    vx
    cmap
    nfcv
    vx
    cC
    nfcv
    nfov
    iunssf
    sylibr
end
