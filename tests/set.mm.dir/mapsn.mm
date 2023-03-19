include "cv.mm"
include "cop.mm"
include "csn.mm"
include "wceq.mm"
include "wrex.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "snex.mm"
include "elmap.mm"
include "wa.mm"
include "wex.mm"
include "crn.mm"
include "wbr.mm"
include "weu.mm"
include "wfn.mm"
include "ffn.mm"
include "snid.mm"
include "fneu.mm"
include "sylancl.mm"
include "cab.mm"
include "euabsn.mm"
include "cima.mm"
include "wrel.mm"
include "frel.mm"
include "relimasn.mm"
include "syl.mm"
include "cdm.mm"
include "imadmrn.mm"
include "fdm.mm"
include "imaeq2d.mm"
include "syl5reqr.mm"
include "eqtr3d.mm"
include "eqeq1d.mm"
include "exbidv.mm"
include "syl5bb.mm"
include "mpbid.mm"
include "vex.mm"
include "eleq2.mm"
include "mpbiri.mm"
include "frn.mm"
include "sseld.mm"
include "syl5.mm"
include "wfo.mm"
include "dffn4.mm"
include "sylib.mm"
include "fof.mm"
include "feq3.mm"
include "syl5ibcom.mm"
include "fsn.mm"
include "syl6ib.mm"
include "jcad.mm"
include "eximdv.mm"
include "mpd.mm"
include "df-rex.mm"
include "sylibr.mm"
include "wss.mm"
include "wf1o.mm"
include "f1osn.mm"
include "f1oeq1.mm"
include "f1of.mm"
include "snssi.mm"
include "fss.mm"
include "syl2an.mm"
include "expcom.mm"
include "rexlimiv.mm"
include "impbii.mm"
include "bitri.mm"
include "abbi2i.mm"

theorem mapsn
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  assume map0.1: |- A e. _V
  assume map0.2: |- B e. _V

  disjoint f y
  disjoint A f
  disjoint A y
  disjoint B f
  disjoint B y
  assert |- ( A ^m { B } ) = { f | E. y e. A f = { <. B , y >. } }

  proof
    vf
    cv
    #
    cB
    vy
    cv
    #
    cop
    csn
    #
    wceq
    #
    vy
    cA
    wrex
    #
    vf
    cA
    cB
    csn
    #
    cmap
    co
    #
    @0
    @6
    wcel
    @5
    cA
    @0
    wf
    #
    @4
    cA
    @5
    @0
    map0.1
    cB
    snex
    elmap
    @7
    @4
    @7
    @1
    cA
    wcel
    #
    @3
    wa
    #
    vy
    wex
    #
    @4
    @7
    @0
    crn
    #
    @1
    csn
    #
    wceq
    #
    vy
    wex
    #
    @10
    @7
    cB
    @1
    @0
    wbr
    #
    vy
    weu
    #
    @14
    @7
    @0
    @5
    wfn
    #
    cB
    @5
    wcel
    @16
    @5
    cA
    @0
    ffn
    #
    cB
    map0.2
    snid
    vy
    @5
    cB
    @0
    fneu
    sylancl
    @16
    @15
    vy
    cab
    #
    @12
    wceq
    #
    vy
    wex
    @7
    @14
    @15
    vy
    euabsn
    @7
    @20
    @13
    vy
    @7
    @19
    @11
    @12
    @7
    @0
    @5
    cima
    #
    @19
    @11
    @7
    @0
    wrel
    @21
    @19
    wceq
    @5
    cA
    @0
    frel
    vy
    cB
    @0
    relimasn
    syl
    @7
    @11
    @0
    @0
    cdm
    #
    cima
    @21
    @0
    imadmrn
    @7
    @22
    @5
    @0
    @5
    cA
    @0
    fdm
    imaeq2d
    syl5reqr
    eqtr3d
    eqeq1d
    exbidv
    syl5bb
    mpbid
    @7
    @13
    @9
    vy
    @7
    @13
    @8
    @3
    @13
    @1
    @11
    wcel
    #
    @7
    @8
    @13
    @23
    @1
    @12
    wcel
    @1
    vy
    vex
    #
    snid
    @11
    @12
    @1
    eleq2
    mpbiri
    @7
    @11
    cA
    @1
    @5
    cA
    @0
    frn
    sseld
    syl5
    @7
    @13
    @5
    @12
    @0
    wf
    #
    @3
    @7
    @5
    @11
    @0
    wf
    #
    @13
    @25
    @7
    @5
    @11
    @0
    wfo
    #
    @26
    @7
    @17
    @27
    @18
    @5
    @0
    dffn4
    sylib
    @5
    @11
    @0
    fof
    syl
    @11
    @12
    @5
    @0
    feq3
    syl5ibcom
    cB
    @1
    @0
    map0.2
    @24
    fsn
    syl6ib
    jcad
    eximdv
    mpd
    @3
    vy
    cA
    df-rex
    sylibr
    @3
    @7
    vy
    cA
    @3
    @8
    @7
    @3
    @25
    @12
    cA
    wss
    @7
    @8
    @3
    @5
    @12
    @0
    wf1o
    #
    @25
    @3
    @28
    @5
    @12
    @2
    wf1o
    cB
    @1
    map0.2
    @24
    f1osn
    @5
    @12
    @0
    @2
    f1oeq1
    mpbiri
    @5
    @12
    @0
    f1of
    syl
    @1
    cA
    snssi
    @5
    @12
    cA
    @0
    fss
    syl2an
    expcom
    rexlimiv
    impbii
    bitri
    abbi2i
end
