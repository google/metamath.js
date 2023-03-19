include "cc0.mm"
include "cdm.mm"
include "wcel.mm"
include "wn.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "rgrx0ndm.mm"
include "neli.mm"
include "ndmfv.mm"
include "ax-mp.mm"

theorem rgrx0nd
  let vv: setvar v
  let cR: class R
  let vg: setvar g
  let vk: setvar k
  assume rgrx0ndm.u: |- R = ( k e. NN0* |-> { g | A. v e. ( Vtx ` g ) ( ( VtxDeg ` g ) ` v ) = k } )

  disjoint g k
  disjoint g v
  disjoint k v
  assert |- ( R ` 0 ) = (/)

  proof
    cc0
    cR
    cdm
    #
    wcel
    wn
    cc0
    cR
    cfv
    c0
    wceq
    cc0
    @0
    vv
    cR
    vg
    vk
    rgrx0ndm.u
    rgrx0ndm
    neli
    cc0
    cR
    ndmfv
    ax-mp
end
