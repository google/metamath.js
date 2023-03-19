include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "ccj.mm"
include "cmul.mm"
include "dipcl.mm"
include "absvalsqd.mm"
include "dipcj.mm"
include "oveq2d.mm"
include "eqtr2d.mm"

theorem ipipcj
  let cA: class A
  let cB: class B
  let cP: class P
  let cU: class U
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume ipcl.1: |- X = ( BaseSet ` U )
  assume ipcl.7: |- P = ( .iOLD ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( ( A P B ) x. ( B P A ) ) = ( ( abs ` ( A P B ) ) ^ 2 ) )

  proof
    cU
    cnv
    wcel
    cA
    cX
    wcel
    cB
    cX
    wcel
    w3a
    #
    cA
    cB
    cP
    co
    #
    cabs
    cfv
    c2
    cexp
    co
    @1
    @1
    ccj
    cfv
    #
    cmul
    co
    @1
    cB
    cA
    cP
    co
    #
    cmul
    co
    @0
    @1
    cA
    cB
    cP
    cU
    cX
    ipcl.1
    ipcl.7
    dipcl
    absvalsqd
    @0
    @2
    @3
    @1
    cmul
    cA
    cB
    cP
    cU
    cX
    ipcl.1
    ipcl.7
    dipcj
    oveq2d
    eqtr2d
end
