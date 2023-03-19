include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "csn.mm"
include "cab.mm"
include "cxp.mm"
include "ciun.mm"
include "cvv.mm"
include "wex.mm"
include "cop.mm"
include "wceq.mm"
include "19.42v.mm"
include "an12.mm"
include "exbii.mm"
include "elxp.mm"
include "excom.mm"
include "weq.mm"
include "velsn.mm"
include "anbi1i.mm"
include "bitri.mm"
include "vex.mm"
include "opeq1.mm"
include "eqeq2d.mm"
include "anbi1d.mm"
include "ceqsexv.mm"
include "nfv.mm"
include "nfsab1.mm"
include "nfan.mm"
include "opeq2.mm"
include "wsb.mm"
include "wb.mm"
include "sbequ12.mm"
include "equcoms.mm"
include "df-clab.mm"
include "syl6rbbr.mm"
include "anbi12d.mm"
include "cbvex.mm"
include "3bitri.mm"
include "anbi2i.mm"
include "3bitr4ri.mm"
include "wrex.mm"
include "eliun.mm"
include "df-rex.mm"
include "elopab.mm"
include "3bitr4i.mm"
include "eqriv.mm"
include "wral.mm"
include "snex.mm"
include "xpexg.mm"
include "sylancr.mm"
include "ralrimiva.mm"
include "iunexg.mm"
include "syl2anc.mm"
include "syl5eqelr.mm"

theorem opabex3d
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume opabex3d.1: |- ( ph -> A e. _V )
  assume opabex3d.2: |- ( ( ph /\ x e. A ) -> { y | ps } e. _V )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint ph x
  disjoint A v
  disjoint A w
  disjoint A z
  disjoint v x
  disjoint w x
  disjoint x z
  disjoint v y
  disjoint w y
  disjoint y z
  disjoint v w
  disjoint v z
  disjoint w z
  disjoint ps v
  disjoint ps w
  disjoint ps z
  assert |- ( ph -> { <. x , y >. | ( x e. A /\ ps ) } e. _V )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wps
    wa
    #
    vx
    vy
    copab
    #
    vx
    cA
    @0
    csn
    #
    wps
    vy
    cab
    #
    cxp
    #
    ciun
    #
    cvv
    vz
    @7
    @3
    @1
    vz
    cv
    #
    @6
    wcel
    #
    wa
    #
    vx
    wex
    #
    @8
    @0
    vy
    cv
    #
    cop
    #
    wceq
    #
    @2
    wa
    #
    vy
    wex
    #
    vx
    wex
    @8
    @7
    wcel
    #
    @8
    @3
    wcel
    @10
    @16
    vx
    @1
    @14
    wps
    wa
    #
    wa
    #
    vy
    wex
    @1
    @18
    vy
    wex
    #
    wa
    @16
    @10
    @1
    @18
    vy
    19.42v
    @15
    @19
    vy
    @14
    @1
    wps
    an12
    exbii
    @9
    @20
    @1
    @9
    @8
    vv
    cv
    #
    vw
    cv
    #
    cop
    #
    wceq
    #
    @21
    @4
    wcel
    #
    @22
    @5
    wcel
    #
    wa
    wa
    #
    vw
    wex
    vv
    wex
    #
    @8
    @0
    @22
    cop
    #
    wceq
    #
    @26
    wa
    #
    vw
    wex
    #
    @20
    vv
    vw
    @8
    @4
    @5
    elxp
    @28
    @27
    vv
    wex
    #
    vw
    wex
    @32
    @27
    vv
    vw
    excom
    @33
    @31
    vw
    @33
    vv
    vx
    weq
    #
    @24
    @26
    wa
    #
    wa
    #
    vv
    wex
    @31
    @27
    @36
    vv
    @27
    @25
    @35
    wa
    @36
    @24
    @25
    @26
    an12
    @25
    @34
    @35
    vv
    @0
    velsn
    anbi1i
    bitri
    exbii
    @35
    @31
    vv
    @0
    vx
    vex
    @34
    @24
    @30
    @26
    @34
    @23
    @29
    @8
    @21
    @0
    @22
    opeq1
    eqeq2d
    anbi1d
    ceqsexv
    bitri
    exbii
    bitri
    @31
    @18
    vw
    vy
    @30
    @26
    vy
    @30
    vy
    nfv
    wps
    vy
    vw
    nfsab1
    nfan
    @18
    vw
    nfv
    vw
    vy
    weq
    #
    @30
    @14
    @26
    wps
    @37
    @29
    @13
    @8
    @22
    @12
    @0
    opeq2
    eqeq2d
    @37
    wps
    wps
    vy
    vw
    wsb
    #
    @26
    wps
    @38
    wb
    vy
    vw
    wps
    vy
    vw
    sbequ12
    equcoms
    wps
    vw
    vy
    df-clab
    syl6rbbr
    anbi12d
    cbvex
    3bitri
    anbi2i
    3bitr4ri
    exbii
    @17
    @9
    vx
    cA
    wrex
    @11
    vx
    @8
    cA
    @6
    eliun
    @9
    vx
    cA
    df-rex
    bitri
    @2
    vx
    vy
    @8
    elopab
    3bitr4i
    eqriv
    wph
    cA
    cvv
    wcel
    @6
    cvv
    wcel
    #
    vx
    cA
    wral
    @7
    cvv
    wcel
    opabex3d.1
    wph
    @39
    vx
    cA
    wph
    @1
    wa
    @4
    cvv
    wcel
    @5
    cvv
    wcel
    @39
    @0
    snex
    opabex3d.2
    @4
    @5
    cvv
    cvv
    xpexg
    sylancr
    ralrimiva
    vx
    cA
    @6
    cvv
    cvv
    iunexg
    syl2anc
    syl5eqelr
end
