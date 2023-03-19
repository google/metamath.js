include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "rsp.mm"
include "ax-mp.mm"

theorem rspec
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume rspec.1: |- A. x e. A ph


  assert |- ( x e. A -> ph )

  proof
    wph
    vx
    cA
    wral
    vx
    cv
    cA
    wcel
    wph
    wi
    rspec.1
    wph
    vx
    cA
    rsp
    ax-mp
end
