include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cfrgr.mm"
include "ciedg.mm"
include "frgr0v.mm"
include "biimp3ar.mm"

theorem frgr0vb
  let cG: class G
  let cW: class W
  let vk: setvar k
  let vl: setvar l
  let vx: setvar x


  assert |- ( ( G e. W /\ ( Vtx ` G ) = (/) /\ ( iEdg ` G ) = (/) ) -> G e. FriendGraph )

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
    cfrgr
    wcel
    cG
    ciedg
    cfv
    c0
    wceq
    cG
    cW
    frgr0v
    biimp3ar
end
