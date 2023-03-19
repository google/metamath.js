include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "ancom.mm"
include "anbi1i.mm"
include "2exbii.mm"
include "excom.mm"
include "bitri.mm"
include "r2exf.mm"
include "3bitr4i.mm"

theorem rexcomf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume ralcomf.1: |- F/_ y A
  assume ralcomf.2: |- F/_ x B

  disjoint x y
  assert |- ( E. x e. A E. y e. B ph <-> E. y e. B E. x e. A ph )

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
    wa
    #
    wph
    wa
    #
    vy
    wex
    vx
    wex
    #
    @1
    @0
    wa
    #
    wph
    wa
    #
    vx
    wex
    vy
    wex
    #
    wph
    vy
    cB
    wrex
    vx
    cA
    wrex
    wph
    vx
    cA
    wrex
    vy
    cB
    wrex
    @4
    @6
    vy
    wex
    vx
    wex
    @7
    @3
    @6
    vx
    vy
    @2
    @5
    wph
    @0
    @1
    ancom
    anbi1i
    2exbii
    @6
    vx
    vy
    excom
    bitri
    wph
    vx
    vy
    cA
    cB
    ralcomf.1
    r2exf
    wph
    vy
    vx
    cB
    cA
    ralcomf.2
    r2exf
    3bitr4i
end
