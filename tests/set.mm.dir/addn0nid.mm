include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "caddc.mm"
include "co.mm"
include "wa.mm"
include "wceq.mm"
include "addid0.mm"
include "biimpd.mm"
include "necon3d.mm"
include "3impia.mm"

theorem addn0nid
  let cX: class X
  let cY: class Y


  assert |- ( ( X e. CC /\ Y e. CC /\ Y =/= 0 ) -> ( X + Y ) =/= X )

  proof
    cX
    cc
    wcel
    #
    cY
    cc
    wcel
    #
    cY
    cc0
    wne
    cX
    cY
    caddc
    co
    #
    cX
    wne
    @0
    @1
    wa
    #
    @2
    cX
    cY
    cc0
    @3
    @2
    cX
    wceq
    cY
    cc0
    wceq
    cX
    cY
    addid0
    biimpd
    necon3d
    3impia
end
