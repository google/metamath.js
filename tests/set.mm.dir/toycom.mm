include "wcel.mm"
include "cc.mm"
include "w3a.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "cabl.mm"
include "cbs.mm"
include "wceq.mm"
include "cv.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseli.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab2.mm"
include "simprbi.mm"
include "eleqtrrd.mm"
include "simp3.mm"
include "eqid.mm"
include "ablcom.mm"
include "syl3anc.mm"
include "oveqi.mm"
include "3eqtr4g.mm"

theorem toycom
  let cA: class A
  let cB: class B
  let cC: class C
  let c.pl: class .+
  let vg: setvar g
  let cK: class K
  assume toycom.1: |- C = { g e. Abel | ( Base ` g ) = CC }
  assume toycom.2: |- .+ = ( +g ` K )

  disjoint K g
  assert |- ( ( K e. C /\ A e. CC /\ B e. CC ) -> ( A .+ B ) = ( B .+ A ) )

  proof
    cK
    cC
    wcel
    #
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    w3a
    #
    cA
    cB
    cK
    cplusg
    cfv
    #
    co
    #
    cB
    cA
    @4
    co
    #
    cA
    cB
    c.pl
    co
    cB
    cA
    c.pl
    co
    @3
    cK
    cabl
    wcel
    #
    cA
    cK
    cbs
    cfv
    #
    wcel
    cB
    @8
    wcel
    @5
    @6
    wceq
    @0
    @1
    @7
    @2
    cC
    cabl
    cK
    cC
    vg
    cv
    #
    cbs
    cfv
    #
    cc
    wceq
    #
    vg
    cabl
    crab
    cabl
    toycom.1
    @11
    vg
    cabl
    ssrab2
    eqsstri
    sseli
    3ad2ant1
    @3
    cA
    cc
    @8
    @0
    @1
    @2
    simp2
    @0
    @1
    @8
    cc
    wceq
    #
    @2
    @0
    @7
    @12
    @11
    @12
    vg
    cK
    cabl
    cC
    @9
    cK
    wceq
    @10
    @8
    cc
    @9
    cK
    cbs
    fveq2
    eqeq1d
    toycom.1
    elrab2
    simprbi
    3ad2ant1
    #
    eleqtrrd
    @3
    cB
    cc
    @8
    @0
    @1
    @2
    simp3
    @13
    eleqtrrd
    @8
    @4
    cK
    cA
    cB
    @8
    eqid
    @4
    eqid
    ablcom
    syl3anc
    c.pl
    @4
    cA
    cB
    toycom.2
    oveqi
    c.pl
    @4
    cB
    cA
    toycom.2
    oveqi
    3eqtr4g
end
