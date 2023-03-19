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
include "btwntriv2.mm"
include "3adant3r2.mm"
include "wi.mm"
include "simpl.mm"
include "simpr2.mm"
include "simpr1.mm"
include "simpr3.mm"
include "axpasch.mm"
include "syl132anc.mm"
include "mpan2d.mm"
include "wceq.mm"
include "simpll.mm"
include "simpr.mm"
include "simplr1.mm"
include "axbtwnid.mm"
include "syl3anc.mm"
include "breq1.mm"
include "biimpd.mm"
include "syl6.mm"
include "impd.mm"
include "rexlimdva.mm"
include "syld.mm"

theorem btwncomim
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N
  let vx: setvar x


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) -> ( A Btwn <. B , C >. -> A Btwn <. C , B >. ) )

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
    cC
    cB
    cop
    #
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
    @10
    cbtwn
    wbr
    #
    @6
    @7
    cC
    cA
    cC
    cop
    cbtwn
    wbr
    #
    @13
    @0
    @2
    @4
    @15
    @3
    cA
    cC
    cN
    btwntriv2
    3adant3r2
    @6
    @0
    @3
    @2
    @4
    @2
    @4
    @7
    @15
    wa
    @13
    wi
    @0
    @5
    simpl
    @0
    @2
    @3
    @4
    simpr2
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
    #
    @16
    @17
    vx
    cB
    cA
    cC
    cA
    cC
    cN
    axpasch
    syl132anc
    mpan2d
    @6
    @12
    @14
    vx
    @1
    @6
    @8
    @1
    wcel
    #
    wa
    #
    @9
    @11
    @14
    @19
    @9
    @8
    cA
    wceq
    #
    @11
    @14
    wi
    @19
    @0
    @18
    @2
    @9
    @20
    wi
    @0
    @5
    @18
    simpll
    @6
    @18
    simpr
    @2
    @3
    @4
    @0
    @18
    simplr1
    @8
    cA
    cN
    axbtwnid
    syl3anc
    @20
    @11
    @14
    @8
    cA
    @10
    cbtwn
    breq1
    biimpd
    syl6
    impd
    rexlimdva
    syld
end
