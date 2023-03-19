include "csh.mm"
include "wcel.mm"
include "cspn.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "cint.mm"
include "chil.mm"
include "wceq.mm"
include "shss.mm"
include "spanval.mm"
include "syl.mm"
include "intmin.mm"
include "eqtrd.mm"

theorem spanid
  let cA: class A
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A e. SH -> ( span ` A ) = A )

  proof
    cA
    csh
    wcel
    #
    cA
    cspn
    cfv
    #
    cA
    vx
    cv
    wss
    vx
    csh
    crab
    cint
    #
    cA
    @0
    cA
    chil
    wss
    @1
    @2
    wceq
    cA
    shss
    vx
    cA
    spanval
    syl
    vx
    cA
    csh
    intmin
    eqtrd
end
