include "wral.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "ax-1.mm"
include "ralrimiv.mm"
include "anim2i.mm"
include "r19.26.mm"
include "sylibr.mm"

theorem r19.27v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A

  disjoint ps x
  assert |- ( ( A. x e. A ph /\ ps ) -> A. x e. A ( ph /\ ps ) )

  proof
    wph
    vx
    cA
    wral
    #
    wps
    wa
    @0
    wps
    vx
    cA
    wral
    #
    wa
    wph
    wps
    wa
    vx
    cA
    wral
    wps
    @1
    @0
    wps
    wps
    vx
    cA
    wps
    vx
    cv
    cA
    wcel
    ax-1
    ralrimiv
    anim2i
    wph
    wps
    vx
    cA
    r19.26
    sylibr
end
