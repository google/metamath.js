include "wral.mm"
include "cv.mm"
include "weq.mm"
include "biidd.mm"
include "rspcv.mm"
include "ralimia.mm"
include "wcel.mm"
include "ax-1.mm"
include "ralrimiv.mm"
include "ralimi.mm"
include "impbii.mm"

theorem rr19.3v
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint A y
  disjoint x y
  disjoint ph y
  assert |- ( A. x e. A A. y e. A ph <-> A. x e. A ph )

  proof
    wph
    vy
    cA
    wral
    #
    vx
    cA
    wral
    wph
    vx
    cA
    wral
    @0
    wph
    vx
    cA
    wph
    wph
    vy
    vx
    cv
    cA
    vy
    vx
    weq
    wph
    biidd
    rspcv
    ralimia
    wph
    @0
    vx
    cA
    wph
    wph
    vy
    cA
    wph
    vy
    cv
    cA
    wcel
    ax-1
    ralrimiv
    ralimi
    impbii
end
