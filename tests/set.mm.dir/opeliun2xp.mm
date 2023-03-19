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
include "nfcsb1v.mm"
include "nfcv.mm"
include "nfxp.mm"
include "nfcri.mm"
include "nfan.mm"
include "weq.mm"
include "sbequ12.mm"
include "csbeq1a.mm"
include "sneq.mm"
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
include "an13.mm"
include "ancom.mm"
include "velsn.mm"
include "equcom.mm"
include "anbi1i.mm"
include "3bitri.mm"
include "exbii.mm"
include "vex.mm"
include "sbequ12r.mm"
include "equcoms.mm"
include "eqcomd.mm"
include "ceqsexv.mm"

theorem opeliun2xp
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vz: setvar z
  let vk: setvar k


  assert |- ( <. C , y >. e. U_ y e. B ( A X. { y } ) <-> ( y e. B /\ C e. A ) )

  proof
    cC
    vy
    cv
    #
    cop
    #
    vy
    cB
    cA
    @0
    csn
    #
    cxp
    #
    ciun
    #
    wcel
    @1
    vx
    cv
    #
    @3
    wcel
    #
    vy
    cB
    wrex
    #
    vx
    cab
    #
    wcel
    @0
    cB
    wcel
    #
    vy
    vz
    wsb
    #
    @1
    vy
    vz
    cv
    #
    cA
    csb
    #
    @11
    csn
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
    cA
    wcel
    #
    wa
    #
    @4
    @8
    @1
    vy
    vx
    cB
    @3
    df-iun
    eleq2i
    @7
    @17
    vx
    @1
    cC
    @0
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
    vy
    wex
    @22
    @6
    vy
    cB
    df-rex
    @24
    @21
    vy
    vz
    @24
    vz
    nfv
    @10
    @20
    vy
    @9
    vy
    vz
    nfs1v
    vy
    vx
    @14
    vy
    @12
    @13
    vy
    @11
    cA
    nfcsb1v
    vy
    @13
    nfcv
    nfxp
    nfcri
    nfan
    vy
    vz
    weq
    #
    @9
    @10
    @6
    @20
    @9
    vy
    vz
    sbequ12
    @25
    @3
    @14
    @5
    @25
    cA
    @12
    @2
    @13
    vy
    @11
    cA
    csbeq1a
    #
    @0
    @11
    sneq
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
    vz
    vy
    weq
    #
    @10
    cC
    @12
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
    @28
    @0
    @13
    wcel
    #
    wa
    #
    wa
    #
    @31
    @29
    wa
    #
    @30
    @15
    @32
    @10
    cC
    @0
    @12
    @13
    opelxp
    anbi2i
    @33
    @31
    @28
    @10
    wa
    #
    wa
    @34
    @10
    @28
    @31
    an13
    @35
    @29
    @31
    @28
    @10
    ancom
    anbi2i
    bitri
    @31
    @27
    @29
    @31
    @25
    @27
    vy
    @11
    velsn
    vy
    vz
    equcom
    bitri
    anbi1i
    3bitri
    exbii
    @29
    @19
    vz
    @0
    vy
    vex
    @27
    @10
    @9
    @28
    @18
    @9
    vz
    vy
    sbequ12r
    @27
    @12
    cA
    cC
    @27
    cA
    @12
    cA
    @12
    wceq
    vy
    vz
    @26
    equcoms
    eqcomd
    eleq2d
    anbi12d
    ceqsexv
    bitri
    3bitri
end
