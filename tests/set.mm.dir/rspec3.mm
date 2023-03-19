include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wral.mm"
include "rspec2.mm"
include "r19.21bi.mm"
include "3impa.mm"

theorem rspec3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  assume rspec3.1: |- A. x e. A A. y e. B A. z e. C ph


  assert |- ( ( x e. A /\ y e. B /\ z e. C ) -> ph )

  proof
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
    vz
    cv
    cC
    wcel
    wph
    @0
    @1
    wa
    wph
    vz
    cC
    wph
    vz
    cC
    wral
    vx
    vy
    cA
    cB
    rspec3.1
    rspec2
    r19.21bi
    3impa
end
