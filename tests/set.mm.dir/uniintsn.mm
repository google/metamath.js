include "cuni.mm"
include "cint.mm"
include "wceq.mm"
include "cv.mm"
include "csn.mm"
include "wex.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "c0.mm"
include "wne.mm"
include "cvv.mm"
include "vn0.mm"
include "inteq.mm"
include "int0.mm"
include "syl6eq.mm"
include "adantl.mm"
include "unieq.mm"
include "uni0.mm"
include "eqeq1.mm"
include "syl5ib.mm"
include "imp.mm"
include "eqtr3d.mm"
include "ex.mm"
include "necon3d.mm"
include "mpi.mm"
include "n0.mm"
include "sylib.mm"
include "cpr.mm"
include "wss.mm"
include "vex.mm"
include "prss.mm"
include "cun.mm"
include "cin.mm"
include "uniss.mm"
include "simpl.mm"
include "sseqtrd.mm"
include "intss.mm"
include "sstrd.mm"
include "unipr.mm"
include "intpr.mm"
include "3sstr3g.mm"
include "inss1.mm"
include "ssun1.mm"
include "sstri.mm"
include "jctir.mm"
include "eqss.mm"
include "uneqin.mm"
include "bitr3i.mm"
include "syl5bi.mm"
include "alrimivv.mm"
include "jca.mm"
include "weu.mm"
include "cab.mm"
include "euabsn.mm"
include "eleq1.mm"
include "eu4.mm"
include "abid2.mm"
include "eqeq1i.mm"
include "exbii.mm"
include "3bitr3i.mm"
include "unisn.mm"
include "intsn.mm"
include "3eqtr4a.mm"
include "exlimiv.mm"
include "impbii.mm"

theorem uniintsn
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let wph: wff ph

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint ph y
  assert |- ( U. A = |^| A <-> E. x A = { x } )

  proof
    cA
    cuni
    #
    cA
    cint
    #
    wceq
    #
    cA
    vx
    cv
    #
    csn
    #
    wceq
    #
    vx
    wex
    #
    @2
    @3
    cA
    wcel
    #
    vx
    wex
    #
    @7
    vy
    cv
    #
    cA
    wcel
    #
    wa
    #
    @3
    @9
    wceq
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    wa
    #
    @6
    @2
    @8
    @14
    @2
    cA
    c0
    wne
    #
    @8
    @2
    cvv
    c0
    wne
    @16
    vn0
    @2
    cA
    c0
    cvv
    c0
    @2
    cA
    c0
    wceq
    #
    cvv
    c0
    wceq
    @2
    @17
    wa
    @1
    cvv
    c0
    @17
    @1
    cvv
    wceq
    @2
    @17
    @1
    c0
    cint
    cvv
    cA
    c0
    inteq
    int0
    syl6eq
    adantl
    @2
    @17
    @1
    c0
    wceq
    #
    @17
    @0
    c0
    wceq
    @2
    @18
    @17
    @0
    c0
    cuni
    c0
    cA
    c0
    unieq
    uni0
    syl6eq
    @0
    @1
    c0
    eqeq1
    syl5ib
    imp
    eqtr3d
    ex
    necon3d
    mpi
    vx
    cA
    n0
    sylib
    @2
    @13
    vx
    vy
    @11
    @3
    @9
    cpr
    #
    cA
    wss
    #
    @2
    @12
    @3
    @9
    cA
    vx
    vex
    #
    vy
    vex
    #
    prss
    @2
    @20
    @12
    @2
    @20
    wa
    #
    @3
    @9
    cun
    #
    @3
    @9
    cin
    #
    wss
    #
    @25
    @24
    wss
    #
    wa
    #
    @12
    @23
    @26
    @27
    @23
    @19
    cuni
    #
    @19
    cint
    #
    @24
    @25
    @23
    @29
    @1
    @30
    @23
    @29
    @0
    @1
    @20
    @29
    @0
    wss
    @2
    @19
    cA
    uniss
    adantl
    @2
    @20
    simpl
    sseqtrd
    @20
    @1
    @30
    wss
    @2
    @19
    cA
    intss
    adantl
    sstrd
    @3
    @9
    @21
    @22
    unipr
    @3
    @9
    @21
    @22
    intpr
    3sstr3g
    @25
    @3
    @24
    @3
    @9
    inss1
    @3
    @9
    ssun1
    sstri
    jctir
    @28
    @24
    @25
    wceq
    @12
    @24
    @25
    eqss
    @3
    @9
    uneqin
    bitr3i
    sylib
    ex
    syl5bi
    alrimivv
    jca
    @7
    vx
    weu
    @7
    vx
    cab
    #
    @4
    wceq
    #
    vx
    wex
    @15
    @6
    @7
    vx
    euabsn
    @7
    @10
    vx
    vy
    @3
    @9
    cA
    eleq1
    eu4
    @32
    @5
    vx
    @31
    cA
    @4
    vx
    cA
    abid2
    eqeq1i
    exbii
    3bitr3i
    sylib
    @5
    @2
    vx
    @5
    @4
    cuni
    @3
    @0
    @1
    @3
    @21
    unisn
    cA
    @4
    unieq
    @5
    @1
    @4
    cint
    @3
    cA
    @4
    inteq
    @3
    @21
    intsn
    syl6eq
    3eqtr4a
    exlimiv
    impbii
end
