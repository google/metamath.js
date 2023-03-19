include "cv.mm"
include "csn.mm"
include "cab.mm"
include "cxp.mm"
include "ciun.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "cvv.mm"
include "wex.mm"
include "cop.mm"
include "wceq.mm"
include "19.42v.mm"
include "an12.mm"
include "exbii.mm"
include "elxp.mm"
include "excom.mm"
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
include "rgen.mm"
include "iunexg.mm"
include "mp2an.mm"
include "eqeltrri.mm"

theorem opabex3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume opabex3.1: |- A e. _V
  assume opabex3.2: |- ( x e. A -> { y | ph } e. _V )

  disjoint A x
  disjoint A y
  disjoint x y
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
  disjoint ph v
  disjoint ph w
  disjoint ph z
  assert |- { <. x , y >. | ( x e. A /\ ph ) } e. _V

  proof
    vx
    cA
    vx
    cv
    #
    csn
    #
    wph
    vy
    cab
    #
    cxp
    #
    ciun
    #
    @0
    cA
    wcel
    #
    wph
    wa
    #
    vx
    vy
    copab
    #
    cvv
    vz
    @4
    @7
    @5
    vz
    cv
    #
    @3
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
    @6
    wa
    #
    vy
    wex
    #
    vx
    wex
    @8
    @4
    wcel
    #
    @8
    @7
    wcel
    @10
    @16
    vx
    @5
    @14
    wph
    wa
    #
    wa
    #
    vy
    wex
    @5
    @18
    vy
    wex
    #
    wa
    @16
    @10
    @5
    @18
    vy
    19.42v
    @15
    @19
    vy
    @14
    @5
    wph
    an12
    exbii
    @9
    @20
    @5
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
    @1
    wcel
    #
    @22
    @2
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
    @1
    @2
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
    @21
    @0
    wceq
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
    wph
    vy
    vw
    nfsab1
    nfan
    @18
    vw
    nfv
    @22
    @12
    wceq
    #
    @30
    @14
    @26
    wph
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
    wph
    wph
    vy
    vw
    wsb
    #
    @26
    wph
    @38
    wb
    vy
    vw
    wph
    vy
    vw
    sbequ12
    equcoms
    wph
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
    @3
    eliun
    @9
    vx
    cA
    df-rex
    bitri
    @6
    vx
    vy
    @8
    elopab
    3bitr4i
    eqriv
    cA
    cvv
    wcel
    @3
    cvv
    wcel
    #
    vx
    cA
    wral
    @4
    cvv
    wcel
    opabex3.1
    @39
    vx
    cA
    @5
    @1
    cvv
    wcel
    @2
    cvv
    wcel
    @39
    @0
    snex
    opabex3.2
    @1
    @2
    cvv
    cvv
    xpexg
    sylancr
    rgen
    vx
    cA
    @3
    cvv
    cvv
    iunexg
    mp2an
    eqeltrri
end
