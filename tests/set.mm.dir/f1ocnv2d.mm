include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "eleq1a.mm"
include "syl.mm"
include "impr.mm"
include "biimpar.mm"
include "exp42.mm"
include "com34.mm"
include "imp32.mm"
include "jcai.mm"
include "biimpa.mm"
include "com23.mm"
include "impbida.mm"
include "f1ocnvd.mm"

theorem f1ocnv2d
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  assume f1od.1: |- F = ( x e. A |-> C )
  assume f1o2d.2: |- ( ( ph /\ x e. A ) -> C e. B )
  assume f1o2d.3: |- ( ( ph /\ y e. B ) -> D e. A )
  assume f1o2d.4: |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( x = D <-> y = C ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C y
  disjoint D x
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( F : A -1-1-onto-> B /\ `' F = ( y e. B |-> D ) ) )

  proof
    wph
    vx
    vy
    cA
    cB
    cC
    cD
    cF
    cB
    cA
    f1od.1
    f1o2d.2
    f1o2d.3
    wph
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cC
    wceq
    #
    wa
    #
    @2
    cB
    wcel
    #
    @0
    cD
    wceq
    #
    wa
    #
    wph
    @4
    wa
    @5
    @6
    wph
    @1
    @3
    @5
    wph
    @1
    wa
    cC
    cB
    wcel
    @3
    @5
    wi
    f1o2d.2
    cC
    cB
    @2
    eleq1a
    syl
    impr
    wph
    @1
    @3
    @5
    @6
    wi
    wph
    @1
    @5
    @3
    @6
    wph
    @1
    @5
    @3
    @6
    wph
    @1
    @5
    wa
    wa
    #
    @6
    @3
    f1o2d.4
    biimpar
    exp42
    com34
    imp32
    jcai
    wph
    @7
    wa
    @1
    @3
    wph
    @5
    @6
    @1
    wph
    @5
    wa
    cD
    cA
    wcel
    @6
    @1
    wi
    f1o2d.3
    cD
    cA
    @0
    eleq1a
    syl
    impr
    wph
    @5
    @6
    @1
    @3
    wi
    wph
    @5
    @1
    @6
    @3
    wph
    @1
    @5
    @6
    @3
    wi
    wph
    @1
    @5
    @6
    @3
    @8
    @6
    @3
    f1o2d.4
    biimpa
    exp42
    com23
    com34
    imp32
    jcai
    impbida
    f1ocnvd
end
