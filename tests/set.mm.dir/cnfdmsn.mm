include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cmpt.mm"
include "cxp.mm"
include "cpw.mm"
include "ccn.mm"
include "co.mm"
include "fmptsnxp.mm"
include "ctopon.mm"
include "cfv.mm"
include "cvv.mm"
include "snex.mm"
include "distopon.mm"
include "mp1i.mm"
include "snidg.mm"
include "adantl.mm"
include "cnconst2.mm"
include "syl3anc.mm"
include "eqeltrd.mm"

theorem cnfdmsn
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vk: setvar k

  disjoint A x
  disjoint B x
  disjoint k x
  assert |- ( ( A e. V /\ B e. W ) -> ( x e. { A } |-> B ) e. ( ~P { A } Cn ~P { B } ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    vx
    cA
    csn
    #
    cB
    cmpt
    @3
    cB
    csn
    #
    cxp
    #
    @3
    cpw
    #
    @4
    cpw
    #
    ccn
    co
    #
    vx
    cA
    cB
    cV
    cW
    fmptsnxp
    @2
    @6
    @3
    ctopon
    cfv
    wcel
    #
    @7
    @4
    ctopon
    cfv
    wcel
    #
    cB
    @4
    wcel
    #
    @5
    @8
    wcel
    @3
    cvv
    wcel
    @9
    @2
    cA
    snex
    @3
    cvv
    distopon
    mp1i
    @4
    cvv
    wcel
    @10
    @2
    cB
    snex
    @4
    cvv
    distopon
    mp1i
    @1
    @11
    @0
    cB
    cW
    snidg
    adantl
    cB
    @6
    @7
    @3
    @4
    cnconst2
    syl3anc
    eqeltrd
end
