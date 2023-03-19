include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cz.mm"
include "cneg.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cdiv.mm"
include "wceq.mm"
include "cr.mm"
include "cn0.mm"
include "wo.mm"
include "wa.mm"
include "elznn0.mm"
include "wi.mm"
include "expneg.mm"
include "ex.mm"
include "ad2antrr.mm"
include "simpll.mm"
include "simprl.mm"
include "recnd.mm"
include "simprr.mm"
include "expneg2.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "expcl.mm"
include "ad2ant2rl.mm"
include "simplr.mm"
include "nn0zd.mm"
include "expne0i.mm"
include "recrecd.mm"
include "eqtr2d.mm"
include "expr.mm"
include "jaod.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "3impia.mm"

theorem expnegz
  let cA: class A
  let cN: class N


  assert |- ( ( A e. CC /\ A =/= 0 /\ N e. ZZ ) -> ( A ^ -u N ) = ( 1 / ( A ^ N ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cN
    cz
    wcel
    #
    cA
    cN
    cneg
    #
    cexp
    co
    #
    c1
    cA
    cN
    cexp
    co
    #
    cdiv
    co
    #
    wceq
    #
    @2
    cN
    cr
    wcel
    #
    cN
    cn0
    wcel
    #
    @3
    cn0
    wcel
    #
    wo
    #
    wa
    @0
    @1
    wa
    #
    @7
    cN
    elznn0
    @12
    @8
    @11
    @7
    @12
    @8
    wa
    @9
    @7
    @10
    @0
    @9
    @7
    wi
    @1
    @8
    @0
    @9
    @7
    cA
    cN
    expneg
    ex
    ad2antrr
    @12
    @8
    @10
    @7
    @12
    @8
    @10
    wa
    #
    wa
    #
    @6
    c1
    c1
    @4
    cdiv
    co
    #
    cdiv
    co
    @4
    @14
    @5
    @15
    c1
    cdiv
    @14
    @0
    cN
    cc
    wcel
    @10
    @5
    @15
    wceq
    @0
    @1
    @13
    simpll
    #
    @14
    cN
    @12
    @8
    @10
    simprl
    recnd
    @12
    @8
    @10
    simprr
    #
    cA
    cN
    expneg2
    syl3anc
    oveq2d
    @14
    @4
    @0
    @10
    @4
    cc
    wcel
    @1
    @8
    cA
    @3
    expcl
    ad2ant2rl
    @14
    @0
    @1
    @3
    cz
    wcel
    @4
    cc0
    wne
    @16
    @0
    @1
    @13
    simplr
    @14
    @3
    @17
    nn0zd
    cA
    @3
    expne0i
    syl3anc
    recrecd
    eqtr2d
    expr
    jaod
    expimpd
    syl5bi
    3impia
end
