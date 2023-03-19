include "ctop.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cnei.mm"
include "cfv.mm"
include "wn.mm"
include "wceq.mm"
include "wa.mm"
include "wss.mm"
include "ssnei.mm"
include "ss0b.mm"
include "sylib.mm"
include "ex.mm"
include "necon3ad.mm"
include "imp.mm"

theorem 0nnei
  let cS: class S
  let cJ: class J


  assert |- ( ( J e. Top /\ S =/= (/) ) -> -. (/) e. ( ( nei ` J ) ` S ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    c0
    wne
    c0
    cS
    cJ
    cnei
    cfv
    cfv
    wcel
    #
    wn
    @0
    @1
    cS
    c0
    @0
    @1
    cS
    c0
    wceq
    #
    @0
    @1
    wa
    cS
    c0
    wss
    @2
    cS
    cJ
    c0
    ssnei
    cS
    ss0b
    sylib
    ex
    necon3ad
    imp
end
