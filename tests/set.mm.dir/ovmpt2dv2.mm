include "co.mm"
include "wceq.mm"
include "cmpt2.mm"
include "eqidd.mm"
include "cv.mm"
include "wa.mm"
include "eqeq2d.mm"
include "biimpd.mm"
include "nfmpt21.mm"
include "nfcv.mm"
include "nfov.mm"
include "nfeq1.mm"
include "nfmpt22.mm"
include "ovmpt2df.mm"
include "mpd.mm"
include "oveq.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"

theorem ovmpt2dv2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let cV: class V
  assume ovmpt2dv2.1: |- ( ph -> A e. C )
  assume ovmpt2dv2.2: |- ( ( ph /\ x = A ) -> B e. D )
  assume ovmpt2dv2.3: |- ( ( ph /\ ( x = A /\ y = B ) ) -> R e. V )
  assume ovmpt2dv2.4: |- ( ( ph /\ ( x = A /\ y = B ) ) -> R = S )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  disjoint S x
  disjoint S y
  assert |- ( ph -> ( F = ( x e. C , y e. D |-> R ) -> ( A F B ) = S ) )

  proof
    wph
    cA
    cB
    cF
    co
    #
    cS
    wceq
    cF
    vx
    vy
    cC
    cD
    cR
    cmpt2
    #
    wceq
    #
    cA
    cB
    @1
    co
    #
    cS
    wceq
    #
    wph
    @1
    @1
    wceq
    @4
    wph
    @1
    eqidd
    wph
    @4
    vx
    vy
    cA
    cB
    cC
    cD
    cR
    @1
    cV
    ovmpt2dv2.1
    ovmpt2dv2.2
    ovmpt2dv2.3
    wph
    vx
    cv
    cA
    wceq
    vy
    cv
    cB
    wceq
    wa
    wa
    #
    @3
    cR
    wceq
    @4
    @5
    cR
    cS
    @3
    ovmpt2dv2.4
    eqeq2d
    biimpd
    vx
    vy
    cC
    cD
    cR
    nfmpt21
    #
    vx
    @3
    cS
    vx
    cA
    cB
    @1
    vx
    cA
    nfcv
    @6
    vx
    cB
    nfcv
    nfov
    nfeq1
    vx
    vy
    cC
    cD
    cR
    nfmpt22
    #
    vy
    @3
    cS
    vy
    cA
    cB
    @1
    vy
    cA
    nfcv
    @7
    vy
    cB
    nfcv
    nfov
    nfeq1
    ovmpt2df
    mpd
    @2
    @0
    @3
    cS
    cA
    cB
    cF
    @1
    oveq
    eqeq1d
    syl5ibrcom
end
