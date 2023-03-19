include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wcel.mm"
include "ne0i.mm"
include "a1d.mm"
include "rexlimiv.mm"

theorem rexn0
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( E. x e. A ph -> A =/= (/) )

  proof
    wph
    cA
    c0
    wne
    #
    vx
    cA
    vx
    cv
    #
    cA
    wcel
    @0
    wph
    cA
    @1
    ne0i
    a1d
    rexlimiv
end
