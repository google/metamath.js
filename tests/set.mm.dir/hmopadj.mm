include "cho.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cado.mm"
include "hmopf.mm"
include "w3a.mm"
include "hmop.mm"
include "eqcomd.mm"
include "3expib.mm"
include "ralrimivv.mm"
include "adjeq.mm"
include "syl3anc.mm"

theorem hmopadj
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( T e. HrmOp -> ( adjh ` T ) = T )

  proof
    cT
    cho
    wcel
    #
    chil
    chil
    cT
    wf
    #
    @1
    vx
    cv
    #
    cT
    cfv
    vy
    cv
    #
    csp
    co
    #
    @2
    @3
    cT
    cfv
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    cT
    cado
    cfv
    cT
    wceq
    cT
    hmopf
    #
    @7
    @0
    @6
    vx
    vy
    chil
    chil
    @0
    @2
    chil
    wcel
    #
    @3
    chil
    wcel
    #
    @6
    @0
    @8
    @9
    w3a
    @5
    @4
    @2
    @3
    cT
    hmop
    eqcomd
    3expib
    ralrimivv
    vx
    vy
    cT
    cT
    adjeq
    syl3anc
end
