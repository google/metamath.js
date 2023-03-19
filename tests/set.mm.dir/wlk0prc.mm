include "cvv.mm"
include "wnel.mm"
include "cvtx.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "cwlks.mm"
include "eqcom.mm"
include "biimpi.mm"
include "vtxvalprc.mm"
include "sylan9eqr.mm"
include "g0wlk0.mm"
include "syl.mm"

theorem wlk0prc
  let cS: class S
  let cG: class G


  assert |- ( ( S e/ _V /\ ( Vtx ` S ) = ( Vtx ` G ) ) -> ( Walks ` G ) = (/) )

  proof
    cS
    cvv
    wnel
    #
    cS
    cvtx
    cfv
    #
    cG
    cvtx
    cfv
    #
    wceq
    #
    wa
    @2
    c0
    wceq
    cG
    cwlks
    cfv
    c0
    wceq
    @3
    @0
    @2
    @1
    c0
    @3
    @2
    @1
    wceq
    @1
    @2
    eqcom
    biimpi
    cS
    vtxvalprc
    sylan9eqr
    cG
    g0wlk0
    syl
end
