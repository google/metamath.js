include "wcel.mm"
include "cima.mm"
include "csb.mm"
include "wceq.mm"
include "cres.mm"
include "crn.mm"
include "idn1.mm"
include "csbresgOLD.mm"
include "e1a.mm"
include "rneq.mm"
include "csbrngOLD.mm"
include "eqeq2.mm"
include "biimpd.mm"
include "e11.mm"
include "wal.mm"
include "df-ima.mm"
include "ax-gen.mm"
include "csbeq2gOLD.mm"
include "e10.mm"
include "biimprcd.mm"
include "in1.mm"

theorem csbima12gALTVD
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( A e. C -> [_ A / x ]_ ( F " B ) = ( [_ A / x ]_ F " [_ A / x ]_ B ) )

  proof
    cA
    cC
    wcel
    #
    vx
    cA
    cF
    cB
    cima
    #
    csb
    #
    vx
    cA
    cF
    csb
    #
    vx
    cA
    cB
    csb
    #
    cima
    #
    wceq
    #
    @0
    @2
    @3
    @4
    cres
    #
    crn
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
    cF
    cB
    cres
    #
    crn
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
    vx
    cA
    @11
    csb
    #
    crn
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
    @0
    @20
    @0
    idn1
    #
    vx
    cA
    cF
    cB
    cC
    csbresgOLD
    e1a
    @16
    @7
    rneq
    e1a
    @0
    @0
    @19
    @21
    vx
    cA
    @11
    cC
    csbrngOLD
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
    @21
    @22
    vx
    cF
    cB
    df-ima
    ax-gen
    vx
    cA
    @1
    @12
    cC
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
    df-ima
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
