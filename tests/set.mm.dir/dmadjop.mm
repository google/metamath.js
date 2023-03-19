include "cado.mm"
include "cdm.mm"
include "wcel.mm"
include "chil.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "dmadjss.mm"
include "sseli.mm"
include "ax-hilex.mm"
include "elmap.mm"
include "sylib.mm"

theorem dmadjop
  let cT: class T
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( T e. dom adjh -> T : ~H --> ~H )

  proof
    cT
    cado
    cdm
    #
    wcel
    cT
    chil
    chil
    cmap
    co
    #
    wcel
    chil
    chil
    cT
    wf
    @0
    @1
    cT
    dmadjss
    sseli
    chil
    chil
    cT
    ax-hilex
    ax-hilex
    elmap
    sylib
end
