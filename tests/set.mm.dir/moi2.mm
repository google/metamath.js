include "wcel.mm"
include "wmo.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "mob2.mm"
include "3expa.mm"
include "biimprd.mm"
include "impr.mm"

theorem moi2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume moi2.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint ps x
  disjoint x y
  disjoint A y
  disjoint ph y
  disjoint ps y
  assert |- ( ( ( A e. B /\ E* x ph ) /\ ( ph /\ ps ) ) -> x = A )

  proof
    cA
    cB
    wcel
    #
    wph
    vx
    wmo
    #
    wa
    #
    wph
    wps
    vx
    cv
    cA
    wceq
    #
    @2
    wph
    wa
    @3
    wps
    @0
    @1
    wph
    @3
    wps
    wb
    wph
    wps
    vx
    cA
    cB
    moi2.1
    mob2
    3expa
    biimprd
    impr
end
