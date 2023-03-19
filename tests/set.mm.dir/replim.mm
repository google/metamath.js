include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cr.mm"
include "wrex.mm"
include "cre.mm"
include "cfv.mm"
include "cim.mm"
include "cnre.mm"
include "wa.mm"
include "crre.mm"
include "crim.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "eqcomd.mm"
include "id.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "rexlimivv.mm"
include "syl.mm"

theorem replim
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. CC -> A = ( ( Re ` A ) + ( _i x. ( Im ` A ) ) ) )

  proof
    cA
    cc
    wcel
    cA
    vx
    cv
    #
    ci
    vy
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vy
    cr
    wrex
    vx
    cr
    wrex
    cA
    cA
    cre
    cfv
    #
    ci
    cA
    cim
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vx
    vy
    cA
    cnre
    @4
    @9
    vx
    vy
    cr
    cr
    @0
    cr
    wcel
    @1
    cr
    wcel
    wa
    #
    @9
    @4
    @3
    @3
    cre
    cfv
    #
    ci
    @3
    cim
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    @10
    @14
    @3
    @10
    @11
    @0
    @13
    @2
    caddc
    @0
    @1
    crre
    @10
    @12
    @1
    ci
    cmul
    @0
    @1
    crim
    oveq2d
    oveq12d
    eqcomd
    @4
    cA
    @3
    @8
    @14
    @4
    id
    @4
    @5
    @11
    @7
    @13
    caddc
    cA
    @3
    cre
    fveq2
    @4
    @6
    @12
    ci
    cmul
    cA
    @3
    cim
    fveq2
    oveq2d
    oveq12d
    eqeq12d
    syl5ibrcom
    rexlimivv
    syl
end
