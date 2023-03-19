include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "cvv.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "a1i.mm"
include "id.mm"
include "riotasvd.mm"
include "mpan2.mm"
include "3impib.mm"

theorem riotasv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume riotasv.1: |- A e. _V
  assume riotasv.2: |- D = ( iota_ x e. A A. y e. B ( ph -> x = C ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint C x
  disjoint ph x
  assert |- ( ( D e. A /\ y e. B /\ ph ) -> D = C )

  proof
    cD
    cA
    wcel
    #
    vy
    cv
    cB
    wcel
    #
    wph
    cD
    cC
    wceq
    #
    @0
    cA
    cvv
    wcel
    @1
    wph
    wa
    @2
    wi
    riotasv.1
    @0
    wph
    vx
    vy
    cA
    cB
    cC
    cD
    cvv
    cD
    wph
    vx
    cv
    cC
    wceq
    wi
    vy
    cB
    wral
    vx
    cA
    crio
    wceq
    @0
    riotasv.2
    a1i
    @0
    id
    riotasvd
    mpan2
    3impib
end
