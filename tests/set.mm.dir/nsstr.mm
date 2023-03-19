include "wss.mm"
include "wn.mm"
include "wa.mm"
include "sstr.mm"
include "ancoms.mm"
include "adantll.mm"
include "simpll.mm"
include "pm2.65da.mm"

theorem nsstr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( -. A C_ B /\ C C_ B ) -> -. A C_ C )

  proof
    cA
    cB
    wss
    #
    wn
    #
    cC
    cB
    wss
    #
    wa
    cA
    cC
    wss
    #
    @0
    @2
    @3
    @0
    @1
    @3
    @2
    @0
    cA
    cC
    cB
    sstr
    ancoms
    adantll
    @1
    @2
    @3
    simpll
    pm2.65da
end
