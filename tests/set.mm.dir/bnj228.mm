include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "wi.mm"
include "rsp.mm"
include "sylbi.mm"
include "impcom.mm"

theorem bnj228
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume bnj228.1: |- ( ph <-> A. x e. A ps )


  assert |- ( ( x e. A /\ ph ) -> ps )

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
    bnj228.1
    wps
    vx
    cA
    rsp
    sylbi
    impcom
end
