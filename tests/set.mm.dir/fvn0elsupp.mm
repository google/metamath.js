include "wcel.mm"
include "wa.mm"
include "wfn.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "csupp.mm"
include "co.mm"
include "simpr.mm"
include "anim12i.mm"
include "cvv.mm"
include "wb.mm"
include "simprl.mm"
include "simpll.mm"
include "0ex.mm"
include "a1i.mm"
include "elsuppfn.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem fvn0elsupp
  let cB: class B
  let cG: class G
  let cV: class V
  let cX: class X


  assert |- ( ( ( B e. V /\ X e. B ) /\ ( G Fn B /\ ( G ` X ) =/= (/) ) ) -> X e. ( G supp (/) ) )

  proof
    cB
    cV
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cG
    cB
    wfn
    #
    cX
    cG
    cfv
    c0
    wne
    #
    wa
    #
    wa
    #
    cX
    cG
    c0
    csupp
    co
    wcel
    #
    @1
    @4
    wa
    #
    @2
    @1
    @5
    @4
    @0
    @1
    simpr
    @3
    @4
    simpr
    anim12i
    @6
    @3
    @0
    c0
    cvv
    wcel
    #
    @7
    @8
    wb
    @2
    @3
    @4
    simprl
    @0
    @1
    @5
    simpll
    @9
    @6
    0ex
    a1i
    cX
    cG
    cV
    cvv
    cB
    c0
    elsuppfn
    syl3anc
    mpbird
end
