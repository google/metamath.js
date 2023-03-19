include "cz.mm"
include "cn0.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "c1.mm"
include "caddc.mm"
include "cop.mm"
include "cmpt2.mm"
include "weq.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "opeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "cbvmpt2v.mm"
include "opnmbllem.mm"

theorem opnmbl
  let cA: class A
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. ( topGen ` ran (,) ) -> A e. dom vol )

  proof
    vz
    vw
    cA
    vx
    vy
    cz
    cn0
    vx
    cv
    #
    c2
    vy
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    @0
    c1
    caddc
    co
    #
    @2
    cdiv
    co
    #
    cop
    #
    cmpt2
    vx
    vy
    vz
    vw
    cz
    cn0
    @6
    vz
    cv
    #
    c2
    vw
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    @7
    c1
    caddc
    co
    #
    @9
    cdiv
    co
    #
    cop
    @7
    @2
    cdiv
    co
    #
    @11
    @2
    cdiv
    co
    #
    cop
    vx
    vz
    weq
    #
    @3
    @13
    @5
    @14
    @0
    @7
    @2
    cdiv
    oveq1
    @15
    @4
    @11
    @2
    cdiv
    @0
    @7
    c1
    caddc
    oveq1
    oveq1d
    opeq12d
    vy
    vw
    weq
    #
    @13
    @10
    @14
    @12
    @16
    @2
    @9
    @7
    cdiv
    @1
    @8
    c2
    cexp
    oveq2
    #
    oveq2d
    @16
    @2
    @9
    @11
    cdiv
    @17
    oveq2d
    opeq12d
    cbvmpt2v
    opnmbllem
end
