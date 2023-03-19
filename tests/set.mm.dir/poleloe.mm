include "cid.mm"
include "cun.mm"
include "wbr.mm"
include "wo.mm"
include "wcel.mm"
include "wceq.mm"
include "brun.mm"
include "ideqg.mm"
include "orbi2d.mm"
include "syl5bb.mm"

theorem poleloe
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V


  assert |- ( B e. V -> ( A ( R u. _I ) B <-> ( A R B \/ A = B ) ) )

  proof
    cA
    cB
    cR
    cid
    cun
    wbr
    cA
    cB
    cR
    wbr
    #
    cA
    cB
    cid
    wbr
    #
    wo
    cB
    cV
    wcel
    #
    @0
    cA
    cB
    wceq
    #
    wo
    cA
    cB
    cR
    cid
    brun
    @2
    @1
    @3
    @0
    cA
    cB
    cV
    ideqg
    orbi2d
    syl5bb
end
