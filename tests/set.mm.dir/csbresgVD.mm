include "wcel.mm"
include "cres.mm"
include "csb.mm"
include "wceq.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "idn1.mm"
include "csbconstg.mm"
include "e1a.mm"
include "xpeq2.mm"
include "csbxpgOLD.mm"
include "eqeq2.mm"
include "biimpd.mm"
include "e11.mm"
include "ineq2.mm"
include "csbingOLD.mm"
include "wal.mm"
include "df-res.mm"
include "ax-gen.mm"
include "csbeq2gOLD.mm"
include "e10.mm"
include "biimprcd.mm"
include "in1.mm"

theorem csbresgVD
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V


  assert |- ( A e. V -> [_ A / x ]_ ( B |` C ) = ( [_ A / x ]_ B |` [_ A / x ]_ C ) )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    cB
    cC
    cres
    #
    csb
    #
    vx
    cA
    cB
    csb
    #
    vx
    cA
    cC
    csb
    #
    cres
    #
    wceq
    #
    @0
    @2
    @3
    @4
    cvv
    cxp
    #
    cin
    #
    wceq
    #
    @5
    @8
    wceq
    #
    @6
    @0
    vx
    cA
    cB
    cC
    cvv
    cxp
    #
    cin
    #
    csb
    #
    @8
    wceq
    #
    @2
    @13
    wceq
    #
    @9
    @0
    @3
    vx
    cA
    @11
    csb
    #
    cin
    #
    @8
    wceq
    #
    @13
    @17
    wceq
    #
    @14
    @0
    @16
    @7
    wceq
    #
    @18
    @0
    @4
    vx
    cA
    cvv
    csb
    #
    cxp
    #
    @7
    wceq
    #
    @16
    @22
    wceq
    #
    @20
    @0
    @21
    cvv
    wceq
    #
    @23
    @0
    @0
    @25
    @0
    idn1
    #
    vx
    cA
    cvv
    cV
    csbconstg
    e1a
    @21
    cvv
    @4
    xpeq2
    e1a
    @0
    @0
    @24
    @26
    vx
    cA
    cC
    cvv
    cV
    csbxpgOLD
    e1a
    @23
    @24
    @20
    @22
    @7
    @16
    eqeq2
    biimpd
    e11
    @16
    @7
    @3
    ineq2
    e1a
    @0
    @0
    @19
    @26
    vx
    cA
    cV
    cB
    @11
    csbingOLD
    e1a
    @18
    @19
    @14
    @17
    @8
    @13
    eqeq2
    biimpd
    e11
    @0
    @0
    @1
    @12
    wceq
    #
    vx
    wal
    @15
    @26
    @27
    vx
    cB
    cC
    df-res
    ax-gen
    vx
    cA
    @1
    @12
    cV
    csbeq2gOLD
    e10
    @14
    @15
    @9
    @13
    @8
    @2
    eqeq2
    biimpd
    e11
    @3
    @4
    df-res
    @10
    @6
    @9
    @5
    @8
    @2
    eqeq2
    biimprcd
    e10
    in1
end
