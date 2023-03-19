include "wsbc.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "cvv.mm"
include "wcel.mm"
include "a1i.mm"
include "wb.mm"
include "3expa.mm"
include "sbcied.mm"
include "sbc2ie.mm"

theorem sbc3ie
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  assume sbc3ie.1: |- A e. _V
  assume sbc3ie.2: |- B e. _V
  assume sbc3ie.3: |- C e. _V
  assume sbc3ie.4: |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C z
  disjoint ps x
  disjoint ps y
  disjoint ps z
  assert |- ( [. A / x ]. [. B / y ]. [. C / z ]. ph <-> ps )

  proof
    wph
    vz
    cC
    wsbc
    wps
    vx
    vy
    cA
    cB
    sbc3ie.1
    sbc3ie.2
    vx
    cv
    cA
    wceq
    #
    vy
    cv
    cB
    wceq
    #
    wa
    #
    wph
    wps
    vz
    cC
    cvv
    cC
    cvv
    wcel
    @2
    sbc3ie.3
    a1i
    @0
    @1
    vz
    cv
    cC
    wceq
    wph
    wps
    wb
    sbc3ie.4
    3expa
    sbcied
    sbc2ie
end
