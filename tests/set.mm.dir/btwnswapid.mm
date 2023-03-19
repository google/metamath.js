include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "wceq.mm"
include "wi.mm"
include "simpl.mm"
include "simpr2.mm"
include "simpr1.mm"
include "simpr3.mm"
include "axpasch.mm"
include "syl132anc.mm"
include "simpll.mm"
include "simpr.mm"
include "simplr1.mm"
include "axbtwnid.mm"
include "syl3anc.mm"
include "simplr2.mm"
include "anim12d.mm"
include "eqtr2.mm"
include "syl6.mm"
include "rexlimdva.mm"
include "syld.mm"

theorem btwnswapid
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N
  let vx: setvar x


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) -> ( ( A Btwn <. B , C >. /\ B Btwn <. A , C >. ) -> A = B ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    cC
    @1
    wcel
    #
    w3a
    #
    wa
    #
    cA
    cB
    cC
    cop
    cbtwn
    wbr
    cB
    cA
    cC
    cop
    cbtwn
    wbr
    wa
    #
    vx
    cv
    #
    cA
    cA
    cop
    cbtwn
    wbr
    #
    @8
    cB
    cB
    cop
    cbtwn
    wbr
    #
    wa
    #
    vx
    @1
    wrex
    #
    cA
    cB
    wceq
    #
    @6
    @0
    @3
    @2
    @4
    @2
    @3
    @7
    @12
    wi
    @0
    @5
    simpl
    @0
    @2
    @3
    @4
    simpr2
    #
    @0
    @2
    @3
    @4
    simpr1
    #
    @0
    @2
    @3
    @4
    simpr3
    @15
    @14
    vx
    cB
    cA
    cC
    cA
    cB
    cN
    axpasch
    syl132anc
    @6
    @11
    @13
    vx
    @1
    @6
    @8
    @1
    wcel
    #
    wa
    #
    @11
    @8
    cA
    wceq
    #
    @8
    cB
    wceq
    #
    wa
    @13
    @17
    @9
    @18
    @10
    @19
    @17
    @0
    @16
    @2
    @9
    @18
    wi
    @0
    @5
    @16
    simpll
    #
    @6
    @16
    simpr
    #
    @2
    @3
    @4
    @0
    @16
    simplr1
    @8
    cA
    cN
    axbtwnid
    syl3anc
    @17
    @0
    @16
    @3
    @10
    @19
    wi
    @20
    @21
    @2
    @3
    @4
    @0
    @16
    simplr2
    @8
    cB
    cN
    axbtwnid
    syl3anc
    anim12d
    @8
    cA
    cB
    eqtr2
    syl6
    rexlimdva
    syld
end
