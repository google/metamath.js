include "ctop.mm"
include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "wceq.mm"
include "wo.mm"
include "cuni.mm"
include "olc.mm"
include "wn.mm"
include "0opn.mm"
include "n0i.mm"
include "syl.mm"
include "pm2.21d.mm"
include "idd.mm"
include "jaod.mm"
include "impbid2.mm"
include "wss.mm"
include "uni0b.mm"
include "sssn.mm"
include "bitr2i.mm"
include "syl6rbb.mm"

theorem 0top
  let cJ: class J


  assert |- ( J e. Top -> ( U. J = (/) <-> J = { (/) } ) )

  proof
    cJ
    ctop
    wcel
    #
    cJ
    c0
    csn
    #
    wceq
    #
    cJ
    c0
    wceq
    #
    @2
    wo
    #
    cJ
    cuni
    c0
    wceq
    #
    @0
    @2
    @4
    @2
    @3
    olc
    @0
    @3
    @2
    @2
    @0
    @3
    @2
    @0
    c0
    cJ
    wcel
    @3
    wn
    cJ
    0opn
    cJ
    c0
    n0i
    syl
    pm2.21d
    @0
    @2
    idd
    jaod
    impbid2
    @5
    cJ
    @1
    wss
    @4
    cJ
    uni0b
    cJ
    c0
    sssn
    bitr2i
    syl6rbb
end
