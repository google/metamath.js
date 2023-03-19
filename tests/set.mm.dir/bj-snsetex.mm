include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "cab.mm"
include "cvv.mm"
include "wex.mm"
include "wi.mm"
include "wceq.mm"
include "elisset.mm"
include "eleq2.mm"
include "abbidv.mm"
include "eleq1.mm"
include "biimpd.mm"
include "syl.mm"
include "eximi.mm"
include "wal.mm"
include "19.35.mm"
include "biimpi.mm"
include "com12.mm"
include "wb.mm"
include "wa.mm"
include "ax-rep.mm"
include "wsb.mm"
include "19.3v.mm"
include "sbbii.mm"
include "csb.mm"
include "wsbc.mm"
include "sbsbc.mm"
include "vex.mm"
include "sbceq2g.mm"
include "ax-mp.mm"
include "bitri.mm"
include "bj-csbsn.mm"
include "eqeq2i.mm"
include "eqtr2.mm"
include "sneqr.mm"
include "sylan2b.mm"
include "syl2anb.mm"
include "gen2.mm"
include "nfa1.mm"
include "mo.mm"
include "mpbir.mm"
include "mpg.mm"
include "bj-sbel1.mm"
include "eleq1i.mm"
include "df-clab.mm"
include "anbi2i.mm"
include "eleq1a.mm"
include "eqcoms.mm"
include "imdistanri.mm"
include "impac.mm"
include "impbii.mm"
include "exbii.mm"
include "snex.mm"
include "isseti.mm"
include "19.42v.mm"
include "mpbiran2.mm"
include "3bitr4ri.mm"
include "bibi2i.mm"
include "albii.mm"
include "mpbi.mm"
include "dfcleq.mm"
include "issetri.mm"
include "ax5e.mm"

theorem bj-snsetex
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let vu: setvar u

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint t x
  disjoint u x
  disjoint y z
  disjoint t y
  disjoint u y
  disjoint A y
  disjoint t z
  disjoint u z
  disjoint A z
  disjoint t u
  disjoint A t
  disjoint A u
  assert |- ( A e. V -> { x | { x } e. A } e. _V )

  proof
    cA
    cV
    wcel
    #
    vx
    cv
    csn
    #
    cA
    wcel
    #
    vx
    cab
    #
    cvv
    wcel
    #
    vy
    wex
    #
    @4
    @0
    @1
    vy
    cv
    #
    wcel
    #
    vx
    cab
    #
    cvv
    wcel
    #
    @4
    wi
    #
    vy
    wex
    #
    @5
    @0
    @6
    cA
    wceq
    #
    vy
    wex
    @11
    vy
    cA
    cV
    elisset
    @12
    @10
    vy
    @12
    @8
    @3
    wceq
    #
    @10
    @12
    @7
    @2
    vx
    @6
    cA
    @1
    eleq2
    abbidv
    @13
    @9
    @4
    @8
    @3
    cvv
    eleq1
    biimpd
    syl
    eximi
    syl
    @9
    @11
    @5
    wi
    vy
    @11
    @9
    vy
    wal
    #
    @5
    @11
    @14
    @5
    wi
    @9
    @4
    vy
    19.35
    biimpi
    com12
    vz
    @8
    vz
    cv
    #
    @8
    wceq
    #
    vz
    wex
    vt
    cv
    #
    @15
    wcel
    #
    @17
    @8
    wcel
    #
    wb
    #
    vt
    wal
    #
    vz
    wex
    #
    @18
    vu
    cv
    #
    @6
    wcel
    #
    @23
    @17
    csn
    #
    wceq
    #
    vz
    wal
    #
    wa
    #
    vu
    wex
    #
    wb
    #
    vt
    wal
    #
    vz
    wex
    #
    @22
    @27
    @17
    @15
    wceq
    #
    wi
    vt
    wal
    vz
    wex
    #
    @32
    vu
    @26
    vy
    vz
    vt
    vu
    ax-rep
    @34
    @27
    @27
    vt
    vz
    wsb
    #
    wa
    @33
    wi
    #
    vz
    wal
    vt
    wal
    @36
    vt
    vz
    @27
    @26
    @26
    vt
    vz
    wsb
    #
    @33
    @35
    @26
    vz
    19.3v
    #
    @27
    @26
    vt
    vz
    @38
    sbbii
    @37
    @26
    @23
    @15
    csn
    #
    wceq
    #
    @33
    @37
    @23
    vt
    @15
    @25
    csb
    #
    wceq
    #
    @40
    @37
    @26
    vt
    @15
    wsbc
    #
    @42
    @26
    vt
    vz
    sbsbc
    @15
    cvv
    wcel
    @43
    @42
    wb
    vz
    vex
    vt
    @15
    @23
    @25
    cvv
    sbceq2g
    ax-mp
    bitri
    @41
    @39
    @23
    vt
    @15
    bj-csbsn
    eqeq2i
    bitri
    @26
    @40
    wa
    @25
    @39
    wceq
    @33
    @23
    @25
    @39
    eqtr2
    @17
    @15
    vt
    vex
    sneqr
    syl
    sylan2b
    syl2anb
    gen2
    @27
    vt
    vz
    @26
    vz
    nfa1
    mo
    mpbir
    mpg
    @31
    @21
    vz
    @30
    @20
    vt
    @29
    @19
    @18
    @7
    vx
    vt
    wsb
    #
    @25
    @6
    wcel
    #
    @19
    @29
    @44
    vx
    @17
    @1
    csb
    #
    @6
    wcel
    @45
    vx
    vt
    @1
    @6
    bj-sbel1
    @46
    @25
    @6
    vx
    @17
    bj-csbsn
    eleq1i
    bitri
    @7
    vt
    vx
    df-clab
    @29
    @45
    @26
    wa
    #
    vu
    wex
    #
    @45
    @28
    @47
    vu
    @28
    @24
    @26
    wa
    #
    @47
    @27
    @26
    @24
    @38
    anbi2i
    @49
    @47
    @26
    @24
    @45
    @24
    @45
    wi
    @25
    @23
    @24
    @25
    @23
    wceq
    @45
    @23
    @6
    @25
    eleq1a
    com12
    eqcoms
    imdistanri
    @45
    @26
    @24
    @25
    @6
    @23
    eleq1a
    impac
    impbii
    bitri
    exbii
    @48
    @45
    @26
    vu
    wex
    vu
    @25
    @17
    snex
    isseti
    @45
    @26
    vu
    19.42v
    mpbiran2
    bitri
    3bitr4ri
    bibi2i
    albii
    exbii
    mpbi
    @16
    @21
    vz
    vt
    @15
    @8
    dfcleq
    exbii
    mpbir
    issetri
    mpg
    syl
    @4
    vy
    ax5e
    syl
end
