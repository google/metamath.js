include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "anassrs.mm"
include "ralbidva.mm"

theorem 2ralbidva
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume 2ralbidva.1: |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( ps <-> ch ) )

  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint A y
  assert |- ( ph -> ( A. x e. A A. y e. B ps <-> A. x e. A A. y e. B ch ) )

  proof
    wph
    wps
    vy
    cB
    wral
    wch
    vy
    cB
    wral
    vx
    cA
    wph
    vx
    cv
    cA
    wcel
    #
    wa
    wps
    wch
    vy
    cB
    wph
    @0
    vy
    cv
    cB
    wcel
    wps
    wch
    wb
    2ralbidva.1
    anassrs
    ralbidva
    ralbidva
end
