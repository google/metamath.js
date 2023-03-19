include "c1.mm"
include "c2.mm"
include "cpr.mm"
include "cpmtr.mm"
include "cfv.mm"
include "cv.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "cpw.mm"
include "crab.mm"
include "wel.mm"
include "csn.mm"
include "cdif.mm"
include "cuni.mm"
include "cif.mm"
include "cmpt.mm"
include "wceq.mm"
include "cvv.mm"
include "wcel.mm"
include "prex.mm"
include "eqid.mm"
include "pmtrfval.mm"
include "ax-mp.mm"
include "cn0.mm"
include "wne.mm"
include "1ex.mm"
include "2nn0.mm"
include "1ne2.mm"
include "pr2pwpr.mm"
include "mp3an.mm"
include "mpteq12i.mm"
include "elsni.mm"
include "wa.mm"
include "eleq2.mm"
include "biimpar.mm"
include "iftrued.mm"
include "wo.mm"
include "wi.mm"
include "elpri.mm"
include "2ex.mm"
include "unisn.mm"
include "simpr.mm"
include "sneq.mm"
include "adantr.mm"
include "difeq12d.mm"
include "difprsn1.mm"
include "syl6eq.mm"
include "unieqd.mm"
include "iftrue.mm"
include "3eqtr4a.mm"
include "ex.mm"
include "difprsn2.mm"
include "nesymi.mm"
include "eqeq1.mm"
include "mtbiri.mm"
include "iffalsed.mm"
include "jaoi.mm"
include "syl.mm"
include "impcom.mm"
include "eqtrd.mm"
include "sylan.mm"
include "mpteq2dva.mm"
include "mpteq2ia.mm"
include "eqtri.mm"

theorem pmtrprfval
  let vz: setvar z
  let vp: setvar p
  let vt: setvar t

  disjoint p z
  disjoint p t
  disjoint t z
  assert |- ( pmTrsp ` { 1 , 2 } ) = ( p e. { { 1 , 2 } } |-> ( z e. { 1 , 2 } |-> if ( z = 1 , 2 , 1 ) ) )

  proof
    c1
    c2
    cpr
    #
    cpmtr
    cfv
    #
    vp
    vt
    cv
    c2o
    cen
    wbr
    vt
    @0
    cpw
    crab
    #
    vz
    @0
    vz
    vp
    wel
    #
    vp
    cv
    #
    vz
    cv
    #
    csn
    #
    cdif
    #
    cuni
    #
    @5
    cif
    #
    cmpt
    #
    cmpt
    #
    vp
    @0
    csn
    #
    vz
    @0
    @5
    c1
    wceq
    #
    c2
    c1
    cif
    #
    cmpt
    #
    cmpt
    #
    @0
    cvv
    wcel
    @1
    @11
    wceq
    c1
    c2
    prex
    vt
    vz
    @0
    @1
    cvv
    vp
    @1
    eqid
    pmtrfval
    ax-mp
    @11
    vp
    @12
    @10
    cmpt
    @16
    vp
    @2
    @10
    @12
    @10
    c1
    cvv
    wcel
    c2
    cn0
    wcel
    c1
    c2
    wne
    #
    @2
    @12
    wceq
    1ex
    2nn0
    1ne2
    c1
    c2
    cvv
    cn0
    vt
    pr2pwpr
    mp3an
    @10
    eqid
    mpteq12i
    vp
    @12
    @10
    @15
    @4
    @12
    wcel
    #
    vz
    @0
    @9
    @14
    @18
    @4
    @0
    wceq
    #
    @5
    @0
    wcel
    #
    @9
    @14
    wceq
    @4
    @0
    elsni
    @19
    @20
    wa
    #
    @9
    @8
    @14
    @21
    @3
    @8
    @5
    @19
    @3
    @20
    @4
    @0
    @5
    eleq2
    biimpar
    iftrued
    @20
    @19
    @8
    @14
    wceq
    #
    @20
    @13
    @5
    c2
    wceq
    #
    wo
    @19
    @22
    wi
    #
    @5
    c1
    c2
    elpri
    @13
    @24
    @23
    @13
    @19
    @22
    @13
    @19
    wa
    #
    c2
    csn
    #
    cuni
    c2
    @8
    @14
    c2
    2ex
    unisn
    @25
    @7
    @26
    @25
    @7
    @0
    c1
    csn
    #
    cdif
    #
    @26
    @25
    @4
    @0
    @6
    @27
    @13
    @19
    simpr
    @13
    @6
    @27
    wceq
    @19
    @5
    c1
    sneq
    adantr
    difeq12d
    @17
    @28
    @26
    wceq
    1ne2
    c1
    c2
    difprsn1
    ax-mp
    syl6eq
    unieqd
    @13
    @14
    c2
    wceq
    @19
    @13
    c2
    c1
    iftrue
    adantr
    3eqtr4a
    ex
    @23
    @19
    @22
    @23
    @19
    wa
    #
    @27
    cuni
    c1
    @8
    @14
    c1
    1ex
    unisn
    @29
    @7
    @27
    @29
    @7
    @0
    @26
    cdif
    #
    @27
    @29
    @4
    @0
    @6
    @26
    @23
    @19
    simpr
    @23
    @6
    @26
    wceq
    @19
    @5
    c2
    sneq
    adantr
    difeq12d
    @17
    @30
    @27
    wceq
    1ne2
    c1
    c2
    difprsn2
    ax-mp
    syl6eq
    unieqd
    @23
    @14
    c1
    wceq
    @19
    @23
    @13
    c2
    c1
    @23
    @13
    c2
    c1
    wceq
    c1
    c2
    1ne2
    nesymi
    @5
    c2
    c1
    eqeq1
    mtbiri
    iffalsed
    adantr
    3eqtr4a
    ex
    jaoi
    syl
    impcom
    eqtrd
    sylan
    mpteq2dva
    mpteq2ia
    eqtri
    eqtri
end
