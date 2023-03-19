include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "ccj.mm"
include "cfv.mm"
include "fveq2.mm"
include "cj0.mm"
include "syl6eq.mm"
include "dipcj.mm"
include "eqeq1d.mm"
include "syl5ib.mm"
include "3com23.mm"
include "impbid.mm"

theorem diporthcom
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


  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( ( A P B ) = 0 <-> ( B P A ) = 0 ) )

  proof
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    cB
    cP
    co
    #
    cc0
    wceq
    #
    cB
    cA
    cP
    co
    #
    cc0
    wceq
    #
    @5
    @4
    ccj
    cfv
    #
    cc0
    wceq
    @3
    @7
    @5
    @8
    cc0
    ccj
    cfv
    #
    cc0
    @4
    cc0
    ccj
    fveq2
    cj0
    syl6eq
    @3
    @8
    @6
    cc0
    cA
    cB
    cP
    cU
    cX
    ipcl.1
    ipcl.7
    dipcj
    eqeq1d
    syl5ib
    @7
    @6
    ccj
    cfv
    #
    cc0
    wceq
    @3
    @5
    @7
    @10
    @9
    cc0
    @6
    cc0
    ccj
    fveq2
    cj0
    syl6eq
    @3
    @10
    @4
    cc0
    @0
    @2
    @1
    @10
    @4
    wceq
    cB
    cA
    cP
    cU
    cX
    ipcl.1
    ipcl.7
    dipcj
    3com23
    eqeq1d
    syl5ib
    impbid
end
