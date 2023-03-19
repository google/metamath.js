include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cusgr.mm"
include "ciedg.mm"
include "usgr0vb.mm"
include "biimp3ar.mm"

theorem usgr0v
  let cG: class G
  let cW: class W


  assert |- ( ( G e. W /\ ( Vtx ` G ) = (/) /\ ( iEdg ` G ) = (/) ) -> G e. USGraph )

  proof
    cG
    cW
    wcel
    cG
    cvtx
    cfv
    c0
    wceq
    cG
    cusgr
    wcel
    cG
    ciedg
    cfv
    c0
    wceq
    cG
    cW
    usgr0vb
    biimp3ar
end
