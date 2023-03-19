include "ctb.mm"
include "wcel.mm"
include "cin.mm"
include "cpw.mm"
include "cuni.mm"
include "wss.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "isbasisg.mm"
include "ibi.mm"
include "wceq.mm"
include "ineq1.mm"
include "pweqd.mm"
include "ineq2d.mm"
include "unieqd.mm"
include "sseq12d.mm"
include "ineq2.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "3impib.mm"

theorem basis1
  let cB: class B
  let cC: class C
  let cD: class D
  let vw: setvar w
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( B e. TopBases /\ C e. B /\ D e. B ) -> ( C i^i D ) C_ U. ( B i^i ~P ( C i^i D ) ) )

  proof
    cB
    ctb
    wcel
    #
    cC
    cB
    wcel
    #
    cD
    cB
    wcel
    #
    cC
    cD
    cin
    #
    cB
    @3
    cpw
    #
    cin
    #
    cuni
    #
    wss
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    cB
    @10
    cpw
    #
    cin
    #
    cuni
    #
    wss
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @1
    @2
    wa
    @7
    @0
    @15
    vx
    vy
    cB
    ctb
    isbasisg
    ibi
    @14
    @7
    cC
    @9
    cin
    #
    cB
    @16
    cpw
    #
    cin
    #
    cuni
    #
    wss
    vx
    vy
    cC
    cD
    cB
    cB
    @8
    cC
    wceq
    #
    @10
    @16
    @13
    @19
    @8
    cC
    @9
    ineq1
    #
    @20
    @12
    @18
    @20
    @11
    @17
    cB
    @20
    @10
    @16
    @21
    pweqd
    ineq2d
    unieqd
    sseq12d
    @9
    cD
    wceq
    #
    @16
    @3
    @19
    @6
    @9
    cD
    cC
    ineq2
    #
    @22
    @18
    @5
    @22
    @17
    @4
    cB
    @22
    @16
    @3
    @23
    pweqd
    ineq2d
    unieqd
    sseq12d
    rspc2v
    syl5com
    3impib
end
