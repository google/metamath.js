include "cr.mm"
include "wss.mm"
include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cmpt.mm"
include "crli.mm"
include "wbr.mm"
include "cv.mm"
include "cle.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "cc0.mm"
include "0re.mm"
include "simpllr.mm"
include "subidd.mm"
include "fveq2d.mm"
include "abs0.mm"
include "syl6eq.mm"
include "rpgt0.mm"
include "ad2antlr.mm"
include "eqbrtrd.mm"
include "a1d.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "sylancr.mm"
include "simplr.mm"
include "simpl.mm"
include "simpr.mm"
include "rlim2.mm"
include "mpbird.mm"

theorem rlimconst
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  assert |- ( ( A C_ RR /\ B e. CC ) -> ( x e. A |-> B ) ~~>r B )

  proof
    cA
    cr
    wss
    #
    cB
    cc
    wcel
    #
    wa
    #
    vx
    cA
    cB
    cmpt
    cB
    crli
    wbr
    vz
    cv
    #
    vx
    cv
    #
    cle
    wbr
    #
    cB
    cB
    cmin
    co
    #
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    wi
    #
    vx
    cA
    wral
    #
    vz
    cr
    wrex
    #
    vy
    crp
    wral
    @2
    @12
    vy
    crp
    @2
    @8
    crp
    wcel
    #
    wa
    #
    cc0
    cr
    wcel
    cc0
    @4
    cle
    wbr
    #
    @9
    wi
    #
    vx
    cA
    wral
    #
    @12
    0re
    @14
    @16
    vx
    cA
    @14
    @4
    cA
    wcel
    #
    wa
    #
    @9
    @15
    @19
    @7
    cc0
    @8
    clt
    @19
    @7
    cc0
    cabs
    cfv
    cc0
    @19
    @6
    cc0
    cabs
    @19
    cB
    @0
    @1
    @13
    @18
    simpllr
    subidd
    fveq2d
    abs0
    syl6eq
    @13
    cc0
    @8
    clt
    wbr
    @2
    @18
    @8
    rpgt0
    ad2antlr
    eqbrtrd
    a1d
    ralrimiva
    @11
    @17
    vz
    cc0
    cr
    @3
    cc0
    wceq
    #
    @10
    @16
    vx
    cA
    @20
    @5
    @15
    @9
    @3
    cc0
    @4
    cle
    breq1
    imbi1d
    ralbidv
    rspcev
    sylancr
    ralrimiva
    @2
    vy
    vz
    vx
    cA
    cB
    cB
    @2
    @1
    vx
    cA
    @0
    @1
    @18
    simplr
    ralrimiva
    @0
    @1
    simpl
    @0
    @1
    simpr
    rlim2
    mpbird
end
