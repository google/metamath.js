include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "cpw.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "simp2.mm"
include "wss.mm"
include "cdif.mm"
include "wa.mm"
include "wex.mm"
include "cvv.mm"
include "isrnsiga.mm"
include "simprbi.mm"
include "simpr3.mm"
include "exlimiv.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "wceq.mm"
include "breq1.mm"
include "unieq.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"

theorem sigaclcu
  let cA: class A
  let cS: class S
  let vo: setvar o
  let vs: setvar s
  let vx: setvar x


  assert |- ( ( S e. U. ran sigAlgebra /\ A e. ~P S /\ A ~<_ _om ) -> U. A e. S )

  proof
    cS
    csiga
    crn
    cuni
    wcel
    #
    cA
    cS
    cpw
    #
    wcel
    #
    cA
    com
    cdom
    wbr
    #
    w3a
    @2
    vx
    cv
    #
    com
    cdom
    wbr
    #
    @4
    cuni
    #
    cS
    wcel
    #
    wi
    #
    vx
    @1
    wral
    #
    @3
    cA
    cuni
    #
    cS
    wcel
    #
    @0
    @2
    @3
    simp2
    @0
    @2
    @9
    @3
    @0
    cS
    vo
    cv
    #
    cpw
    wss
    #
    @12
    cS
    wcel
    #
    @12
    @4
    cdif
    cS
    wcel
    vx
    cS
    wral
    #
    @9
    w3a
    wa
    #
    vo
    wex
    #
    @9
    @0
    cS
    cvv
    wcel
    @17
    vx
    cS
    vo
    isrnsiga
    simprbi
    @16
    @9
    vo
    @13
    @14
    @15
    @9
    simpr3
    exlimiv
    syl
    3ad2ant1
    @0
    @2
    @3
    simp3
    @8
    @3
    @11
    wi
    vx
    cA
    @1
    @4
    cA
    wceq
    #
    @5
    @3
    @7
    @11
    @4
    cA
    com
    cdom
    breq1
    @18
    @6
    @10
    cS
    @4
    cA
    unieq
    eleq1d
    imbi12d
    rspcv
    syl3c
end
