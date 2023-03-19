include "cch.mm"
include "wcel.mm"
include "cat.mm"
include "wa.mm"
include "cin.mm"
include "c0h.mm"
include "wceq.mm"
include "cmd.mm"
include "wbr.mm"
include "chj.mm"
include "co.mm"
include "ccv.mm"
include "cvp.mm"
include "wi.mm"
include "atelch.mm"
include "cvexch.mm"
include "cvmd.mm"
include "3expia.mm"
include "sylbird.mm"
include "sylan2.mm"
include "sylbid.mm"
include "wn.mm"
include "wss.mm"
include "atnssm0.mm"
include "con1bid.mm"
include "ssmd2.mm"
include "3com12.mm"
include "syl3an2.mm"
include "pm2.61d.mm"

theorem atmd2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. HAtoms ) -> A MH B )

  proof
    cA
    cch
    wcel
    #
    cB
    cat
    wcel
    #
    wa
    #
    cA
    cB
    cin
    #
    c0h
    wceq
    #
    cA
    cB
    cmd
    wbr
    #
    @2
    @4
    cA
    cA
    cB
    chj
    co
    ccv
    wbr
    #
    @5
    cA
    cB
    cvp
    @1
    @0
    cB
    cch
    wcel
    #
    @6
    @5
    wi
    cB
    atelch
    #
    @0
    @7
    wa
    @6
    @3
    cB
    ccv
    wbr
    #
    @5
    cA
    cB
    cvexch
    @0
    @7
    @9
    @5
    cA
    cB
    cvmd
    3expia
    sylbird
    sylan2
    sylbid
    @2
    @4
    wn
    cB
    cA
    wss
    #
    @5
    @2
    @10
    @4
    cA
    cB
    atnssm0
    con1bid
    @0
    @1
    @10
    @5
    @1
    @0
    @7
    @10
    @5
    @8
    @7
    @0
    @10
    @5
    cB
    cA
    ssmd2
    3com12
    syl3an2
    3expia
    sylbid
    pm2.61d
end
