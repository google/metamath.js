include "cv.mm"
include "wbr.mm"
include "copab.mm"
include "wa.mm"
include "cvv.mm"
include "pm4.24.mm"
include "opabbii.mm"
include "opabresexd.mm"
include "syl5eqel.mm"

theorem opabbrfexd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cU: class U
  let cV: class V
  let cW: class W
  let vk: setvar k
  assume opabresexd.x: |- ( ( ph /\ x R y ) -> x e. C )
  assume opabresexd.y: |- ( ( ph /\ x R y ) -> y : A --> B )
  assume opabresexd.a: |- ( ( ph /\ x e. C ) -> A e. U )
  assume opabresexd.b: |- ( ( ph /\ x e. C ) -> B e. V )
  assume opabresexd.c: |- ( ph -> C e. W )

  disjoint A y
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint k x
  assert |- ( ph -> { <. x , y >. | x R y } e. _V )

  proof
    wph
    vx
    cv
    vy
    cv
    cR
    wbr
    #
    vx
    vy
    copab
    @0
    @0
    wa
    #
    vx
    vy
    copab
    cvv
    @0
    @1
    vx
    vy
    @0
    pm4.24
    opabbii
    wph
    @0
    vx
    vy
    cA
    cB
    cC
    cR
    cU
    cV
    cW
    opabresexd.x
    opabresexd.y
    opabresexd.a
    opabresexd.b
    opabresexd.c
    opabresexd
    syl5eqel
end
