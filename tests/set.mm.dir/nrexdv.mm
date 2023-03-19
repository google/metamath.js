include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "ralrimiva.mm"
include "ralnex.mm"
include "sylib.mm"

theorem nrexdv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume nrexdv.1: |- ( ( ph /\ x e. A ) -> -. ps )

  disjoint ph x
  assert |- ( ph -> -. E. x e. A ps )

  proof
    wph
    wps
    wn
    #
    vx
    cA
    wral
    wps
    vx
    cA
    wrex
    wn
    wph
    @0
    vx
    cA
    nrexdv.1
    ralrimiva
    wps
    vx
    cA
    ralnex
    sylib
end
