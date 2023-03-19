include "cq.mm"
include "wcel.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cn.mm"
include "wrex.mm"
include "cz.mm"
include "cmul.mm"
include "elq.mm"
include "rexcom.mm"
include "wa.mm"
include "cc.mm"
include "zcn.mm"
include "adantl.mm"
include "nncn.mm"
include "adantr.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0.mm"
include "divcan1d.mm"
include "simpr.mm"
include "eqeltrd.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "reximia.mm"
include "sylbi.mm"

theorem qmulz
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( A e. QQ -> E. x e. NN ( A x. x ) e. ZZ )

  proof
    cA
    cq
    wcel
    cA
    vy
    cv
    #
    vx
    cv
    #
    cdiv
    co
    #
    wceq
    #
    vx
    cn
    wrex
    vy
    cz
    wrex
    #
    cA
    @1
    cmul
    co
    #
    cz
    wcel
    #
    vx
    cn
    wrex
    #
    vy
    vx
    cA
    elq
    @4
    @3
    vy
    cz
    wrex
    #
    vx
    cn
    wrex
    @7
    @3
    vy
    vx
    cz
    cn
    rexcom
    @8
    @6
    vx
    cn
    @1
    cn
    wcel
    #
    @3
    @6
    vy
    cz
    @9
    @0
    cz
    wcel
    #
    wa
    #
    @6
    @3
    @2
    @1
    cmul
    co
    #
    cz
    wcel
    @11
    @12
    @0
    cz
    @11
    @0
    @1
    @10
    @0
    cc
    wcel
    @9
    @0
    zcn
    adantl
    @9
    @1
    cc
    wcel
    @10
    @1
    nncn
    adantr
    @9
    @1
    cc0
    wne
    @10
    @1
    nnne0
    adantr
    divcan1d
    @9
    @10
    simpr
    eqeltrd
    @3
    @5
    @12
    cz
    cA
    @2
    @1
    cmul
    oveq1
    eleq1d
    syl5ibrcom
    rexlimdva
    reximia
    sylbi
    sylbi
end
