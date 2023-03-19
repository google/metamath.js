include "cxrn.mm"
include "c1st.mm"
include "cvv.mm"
include "cxp.mm"
include "cres.mm"
include "ccnv.mm"
include "ccom.mm"
include "c2nd.mm"
include "cin.mm"
include "df-xrn.mm"
include "inss1.mm"
include "relco.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wcel.mm"
include "cop.mm"
include "vex.mm"
include "brcnv.mm"
include "brres.mm"
include "simprbi.mm"
include "sylbi.mm"
include "adantl.mm"
include "exlimiv.mm"
include "opelco.mm"
include "opelxp.mm"
include "mpbiran.mm"
include "3imtr4i.mm"
include "relssi.mm"
include "sstri.mm"
include "eqsstri.mm"

theorem xrnss3v
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A |X. B ) C_ ( _V X. ( _V X. _V ) )

  proof
    cA
    cB
    cxrn
    c1st
    cvv
    cvv
    cxp
    #
    cres
    #
    ccnv
    #
    cA
    ccom
    #
    c2nd
    @0
    cres
    ccnv
    cB
    ccom
    #
    cin
    #
    cvv
    @0
    cxp
    #
    cA
    cB
    df-xrn
    @5
    @3
    @6
    @3
    @4
    inss1
    vx
    vy
    @3
    @6
    @2
    cA
    relco
    vx
    cv
    #
    vz
    cv
    #
    cA
    wbr
    #
    @8
    vy
    cv
    #
    @2
    wbr
    #
    wa
    #
    vz
    wex
    @10
    @0
    wcel
    #
    @7
    @10
    cop
    #
    @3
    wcel
    @14
    @6
    wcel
    #
    @12
    @13
    vz
    @11
    @13
    @9
    @11
    @10
    @8
    @1
    wbr
    #
    @13
    @8
    @10
    @1
    vz
    vex
    #
    vy
    vex
    #
    brcnv
    @16
    @10
    @8
    c1st
    wbr
    @13
    @10
    @8
    c1st
    @0
    @17
    brres
    simprbi
    sylbi
    adantl
    exlimiv
    vz
    @7
    @10
    @2
    cA
    vx
    vex
    #
    @18
    opelco
    @15
    @7
    cvv
    wcel
    @13
    @19
    @7
    @10
    cvv
    @0
    opelxp
    mpbiran
    3imtr4i
    relssi
    sstri
    eqsstri
end
