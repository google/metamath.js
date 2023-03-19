include "cv.mm"
include "wf.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "mapex.mm"
include "syl2anc.mm"
include "opabresex0d.mm"

theorem opabresexd
  let wph: wff ph
  let wps: wff ps
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
  assert |- ( ph -> { <. x , y >. | ( x R y /\ ps ) } e. _V )

  proof
    wph
    wps
    cA
    cB
    vy
    cv
    wf
    #
    vx
    vy
    cC
    cR
    cvv
    cW
    opabresexd.x
    opabresexd.y
    wph
    vx
    cv
    cC
    wcel
    wa
    cA
    cU
    wcel
    cB
    cV
    wcel
    @0
    vy
    cab
    cvv
    wcel
    opabresexd.a
    opabresexd.b
    cA
    cB
    cU
    cV
    vy
    mapex
    syl2anc
    opabresexd.c
    opabresex0d
end
