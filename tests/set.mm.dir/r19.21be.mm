include "wi.mm"
include "cv.mm"
include "wcel.mm"
include "r19.21bi.mm"
include "expcom.mm"
include "rgen.mm"

theorem r19.21be
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume r19.21be.1: |- ( ph -> A. x e. A ps )


  assert |- A. x e. A ( ph -> ps )

  proof
    wph
    wps
    wi
    vx
    cA
    wph
    vx
    cv
    cA
    wcel
    wps
    wph
    wps
    vx
    cA
    r19.21be.1
    r19.21bi
    expcom
    rgen
end
