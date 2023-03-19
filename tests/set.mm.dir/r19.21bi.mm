include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "wi.mm"
include "rsp.mm"
include "syl.mm"
include "imp.mm"

theorem r19.21bi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume r19.21bi.1: |- ( ph -> A. x e. A ps )


  assert |- ( ( ph /\ x e. A ) -> ps )

  proof
    wph
    vx
    cv
    cA
    wcel
    #
    wps
    wph
    wps
    vx
    cA
    wral
    @0
    wps
    wi
    r19.21bi.1
    wps
    vx
    cA
    rsp
    syl
    imp
end
