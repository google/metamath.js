include "cq.mm"
include "wcel.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cn.mm"
include "wrex.mm"
include "cz.mm"
include "cneg.mm"
include "elq.mm"
include "wa.mm"
include "cc.mm"
include "zcn.mm"
include "adantr.mm"
include "nncn.mm"
include "adantl.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0.mm"
include "divnegd.mm"
include "znegcl.mm"
include "znq.mm"
include "sylan.mm"
include "eqeltrd.mm"
include "negeq.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "rexlimivv.mm"
include "sylbi.mm"

theorem qnegcl
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cB: class B


  assert |- ( A e. QQ -> -u A e. QQ )

  proof
    cA
    cq
    wcel
    cA
    vx
    cv
    #
    vy
    cv
    #
    cdiv
    co
    #
    wceq
    #
    vy
    cn
    wrex
    vx
    cz
    wrex
    cA
    cneg
    #
    cq
    wcel
    #
    vx
    vy
    cA
    elq
    @3
    @5
    vx
    vy
    cz
    cn
    @0
    cz
    wcel
    #
    @1
    cn
    wcel
    #
    wa
    #
    @5
    @3
    @2
    cneg
    #
    cq
    wcel
    @8
    @9
    @0
    cneg
    #
    @1
    cdiv
    co
    #
    cq
    @8
    @0
    @1
    @6
    @0
    cc
    wcel
    @7
    @0
    zcn
    adantr
    @7
    @1
    cc
    wcel
    @6
    @1
    nncn
    adantl
    @7
    @1
    cc0
    wne
    @6
    @1
    nnne0
    adantl
    divnegd
    @6
    @10
    cz
    wcel
    @7
    @11
    cq
    wcel
    @0
    znegcl
    @10
    @1
    znq
    sylan
    eqeltrd
    @3
    @4
    @9
    cq
    cA
    @2
    negeq
    eleq1d
    syl5ibrcom
    rexlimivv
    sylbi
end
