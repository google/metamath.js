include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "rspec.mm"
include "r19.21bi.mm"

theorem rspec2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume rspec2.1: |- A. x e. A A. y e. B ph


  assert |- ( ( x e. A /\ y e. B ) -> ph )

  proof
    vx
    cv
    cA
    wcel
    wph
    vy
    cB
    wph
    vy
    cB
    wral
    vx
    cA
    rspec2.1
    rspec
    r19.21bi
end
