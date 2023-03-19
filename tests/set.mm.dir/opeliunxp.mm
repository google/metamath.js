include "cv.mm"
include "cop.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "wcel.mm"
include "wrex.mm"
include "cab.mm"
include "wsb.mm"
include "csb.mm"
include "wa.mm"
include "wex.mm"
include "df-iun.mm"
include "eleq2i.mm"
include "opex.mm"
include "wceq.mm"
include "df-rex.mm"
include "nfv.mm"
include "nfs1v.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfxp.mm"
include "nfcri.mm"
include "nfan.mm"
include "sbequ12.mm"
include "sneq.mm"
include "csbeq1a.mm"
include "xpeq12d.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "cbvex.mm"
include "bitri.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "syl5bb.mm"
include "elab.mm"
include "opelxp.mm"
include "anbi2i.mm"
include "an12.mm"
include "velsn.mm"
include "equcom.mm"
include "anbi1i.mm"
include "3bitri.mm"
include "exbii.mm"
include "sbequ12r.mm"
include "equcoms.mm"
include "eqcomd.mm"
include "equsexvw.mm"

theorem opeliunxp
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  let vz: setvar z


  assert |- ( <. x , C >. e. U_ x e. A ( { x } X. B ) <-> ( x e. A /\ C e. B ) )

  proof
    vx
    cv
    #
    cC
    cop
    #
    vx
    cA
    @0
    csn
    #
    cB
    cxp
    #
    ciun
    #
    wcel
    @1
    vy
    cv
    #
    @3
    wcel
    #
    vx
    cA
    wrex
    #
    vy
    cab
    #
    wcel
    @0
    cA
    wcel
    #
    vx
    vz
    wsb
    #
    @1
    vz
    cv
    #
    csn
    #
    vx
    @11
    cB
    csb
    #
    cxp
    #
    wcel
    #
    wa
    #
    vz
    wex
    #
    @9
    cC
    cB
    wcel
    #
    wa
    #
    @4
    @8
    @1
    vx
    vy
    cA
    @3
    df-iun
    eleq2i
    @7
    @17
    vy
    @1
    @0
    cC
    opex
    @7
    @10
    @5
    @14
    wcel
    #
    wa
    #
    vz
    wex
    #
    @5
    @1
    wceq
    #
    @17
    @7
    @9
    @6
    wa
    #
    vx
    wex
    @22
    @6
    vx
    cA
    df-rex
    @24
    @21
    vx
    vz
    @24
    vz
    nfv
    @10
    @20
    vx
    @9
    vx
    vz
    nfs1v
    vx
    vy
    @14
    vx
    @12
    @13
    vx
    @12
    nfcv
    vx
    @11
    cB
    nfcsb1v
    nfxp
    nfcri
    nfan
    @0
    @11
    wceq
    #
    @9
    @10
    @6
    @20
    @9
    vx
    vz
    sbequ12
    @25
    @3
    @14
    @5
    @25
    @2
    @12
    cB
    @13
    @0
    @11
    sneq
    vx
    @11
    cB
    csbeq1a
    #
    xpeq12d
    eleq2d
    anbi12d
    cbvex
    bitri
    @23
    @21
    @16
    vz
    @23
    @20
    @15
    @10
    @5
    @1
    @14
    eleq1
    anbi2d
    exbidv
    syl5bb
    elab
    @17
    @11
    @0
    wceq
    #
    @10
    cC
    @13
    wcel
    #
    wa
    #
    wa
    #
    vz
    wex
    @19
    @16
    @30
    vz
    @16
    @10
    @0
    @12
    wcel
    #
    @28
    wa
    #
    wa
    @31
    @29
    wa
    @30
    @15
    @32
    @10
    @0
    cC
    @12
    @13
    opelxp
    anbi2i
    @10
    @31
    @28
    an12
    @31
    @27
    @29
    @31
    @25
    @27
    vx
    @11
    velsn
    vx
    vz
    equcom
    bitri
    anbi1i
    3bitri
    exbii
    @29
    @19
    vz
    vx
    @27
    @10
    @9
    @28
    @18
    @9
    vz
    vx
    sbequ12r
    @27
    @13
    cB
    cC
    @27
    cB
    @13
    cB
    @13
    wceq
    vx
    vz
    @26
    equcoms
    eqcomd
    eleq2d
    anbi12d
    equsexvw
    bitri
    3bitri
end
