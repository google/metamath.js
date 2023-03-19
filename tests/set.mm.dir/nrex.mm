include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "rgen.mm"
include "ralnex.mm"
include "mpbi.mm"

theorem nrex
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume nrex.1: |- ( x e. A -> -. ps )


  assert |- -. E. x e. A ps

  proof
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
    @0
    vx
    cA
    nrex.1
    rgen
    wps
    vx
    cA
    ralnex
    mpbi
end
