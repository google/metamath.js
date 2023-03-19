include "wss.mm"
include "wral.mm"
include "crab.mm"
include "ralrimiva.mm"
include "ssrab.mm"
include "sylanbrc.mm"

theorem ssrabdv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume ssrabdv.1: |- ( ph -> B C_ A )
  assume ssrabdv.2: |- ( ( ph /\ x e. B ) -> ps )

  disjoint A x
  disjoint B x
  disjoint ph x
  assert |- ( ph -> B C_ { x e. A | ps } )

  proof
    wph
    cB
    cA
    wss
    wps
    vx
    cB
    wral
    cB
    wps
    vx
    cA
    crab
    wss
    ssrabdv.1
    wph
    wps
    vx
    cB
    ssrabdv.2
    ralrimiva
    wps
    vx
    cA
    cB
    ssrab
    sylanbrc
end
