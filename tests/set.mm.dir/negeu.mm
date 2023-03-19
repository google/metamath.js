include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wreu.mm"
include "wrex.mm"
include "cnegex.mm"
include "adantr.mm"
include "wb.mm"
include "wral.mm"
include "simpl.mm"
include "simpr.mm"
include "addcl.mm"
include "syl2anr.mm"
include "simplrr.mm"
include "oveq1d.mm"
include "simplll.mm"
include "simplrl.mm"
include "simpllr.mm"
include "addassd.mm"
include "addid2d.mm"
include "3eqtr3rd.mm"
include "eqeq2d.mm"
include "addcld.mm"
include "addcand.mm"
include "bitrd.mm"
include "ralrimiva.mm"
include "reu6i.mm"
include "syl2anc.mm"
include "rexlimddv.mm"

theorem negeu
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( ( A e. CC /\ B e. CC ) -> E! x e. CC ( A + x ) = B )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    vy
    cv
    #
    caddc
    co
    #
    cc0
    wceq
    #
    cA
    vx
    cv
    #
    caddc
    co
    #
    cB
    wceq
    #
    vx
    cc
    wreu
    #
    vy
    cc
    @0
    @5
    vy
    cc
    wrex
    @1
    vy
    cA
    cnegex
    adantr
    @2
    @3
    cc
    wcel
    #
    @5
    wa
    #
    wa
    #
    @3
    cB
    caddc
    co
    #
    cc
    wcel
    #
    @8
    @6
    @13
    wceq
    #
    wb
    #
    vx
    cc
    wral
    @9
    @11
    @10
    @1
    @14
    @2
    @10
    @5
    simpl
    @0
    @1
    simpr
    @3
    cB
    addcl
    syl2anr
    @12
    @16
    vx
    cc
    @12
    @6
    cc
    wcel
    #
    wa
    #
    @8
    @7
    cA
    @13
    caddc
    co
    #
    wceq
    @15
    @18
    cB
    @19
    @7
    @18
    @4
    cB
    caddc
    co
    cc0
    cB
    caddc
    co
    @19
    cB
    @18
    @4
    cc0
    cB
    caddc
    @2
    @10
    @5
    @17
    simplrr
    oveq1d
    @18
    cA
    @3
    cB
    @0
    @1
    @11
    @17
    simplll
    #
    @2
    @10
    @5
    @17
    simplrl
    #
    @0
    @1
    @11
    @17
    simpllr
    #
    addassd
    @18
    cB
    @22
    addid2d
    3eqtr3rd
    eqeq2d
    @18
    cA
    @6
    @13
    @20
    @12
    @17
    simpr
    @18
    @3
    cB
    @21
    @22
    addcld
    addcand
    bitrd
    ralrimiva
    @8
    vx
    cc
    @13
    reu6i
    syl2anc
    rexlimddv
end
