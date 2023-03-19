include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "rsp.mm"
include "syl6.mm"
include "impd.mm"

theorem rsp2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B


  assert |- ( A. x e. A A. y e. B ph -> ( ( x e. A /\ y e. B ) -> ph ) )

  proof
    wph
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    vx
    cv
    cA
    wcel
    #
    vy
    cv
    cB
    wcel
    #
    wph
    @1
    @2
    @0
    @3
    wph
    wi
    @0
    vx
    cA
    rsp
    wph
    vy
    cB
    rsp
    syl6
    impd
end
