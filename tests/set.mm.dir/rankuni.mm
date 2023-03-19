include "cvv.mm"
include "wcel.mm"
include "cuni.mm"
include "crnk.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "unieq.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "unieqd.mm"
include "eqeq12d.mm"
include "wrex.mm"
include "cab.mm"
include "ciun.mm"
include "vex.mm"
include "rankuni2.mm"
include "fvex.mm"
include "dfiun2.mm"
include "eqtri.mm"
include "wa.mm"
include "wex.mm"
include "df-rex.mm"
include "rankel.mm"
include "anim1i.mm"
include "eximi.mm"
include "19.42v.mm"
include "eleq1.mm"
include "pm5.32ri.mm"
include "exbii.mm"
include "simpl.mm"
include "cr1.mm"
include "cdm.mm"
include "con0.mm"
include "rankon.mm"
include "oneli.mm"
include "wfn.mm"
include "r1fnon.mm"
include "fndm.mm"
include "ax-mp.mm"
include "syl6eleqr.mm"
include "rankr1id.mm"
include "sylib.mm"
include "eqcomd.mm"
include "eqeq2d.mm"
include "spcev.mm"
include "syl.mm"
include "ancli.mm"
include "impbii.mm"
include "3bitr3i.mm"
include "sylbi.mm"
include "abssi.mm"
include "unissi.mm"
include "eqsstri.mm"
include "csuc.mm"
include "cpw.mm"
include "wss.mm"
include "pwuni.mm"
include "vuniex.mm"
include "pwex.mm"
include "rankss.mm"
include "rankpw.mm"
include "sseqtri.mm"
include "onunisuci.mm"
include "eqssi.mm"
include "vtoclg.mm"
include "wn.mm"
include "c0.mm"
include "uniexb.mm"
include "fvprc.mm"
include "sylnbi.mm"
include "uni0.mm"
include "syl6eqr.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem rankuni
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( rank ` U. A ) = U. ( rank ` A )

  proof
    cA
    cvv
    wcel
    #
    cA
    cuni
    #
    crnk
    cfv
    #
    cA
    crnk
    cfv
    #
    cuni
    #
    wceq
    #
    vx
    cv
    #
    cuni
    #
    crnk
    cfv
    #
    @6
    crnk
    cfv
    #
    cuni
    #
    wceq
    @5
    vx
    cA
    cvv
    @6
    cA
    wceq
    #
    @8
    @2
    @10
    @4
    @11
    @7
    @1
    crnk
    @6
    cA
    unieq
    fveq2d
    @11
    @9
    @3
    @6
    cA
    crnk
    fveq2
    unieqd
    eqeq12d
    @8
    @10
    @8
    vy
    cv
    #
    vz
    cv
    #
    crnk
    cfv
    #
    wceq
    #
    vz
    @6
    wrex
    #
    vy
    cab
    #
    cuni
    #
    @10
    @8
    vz
    @6
    @14
    ciun
    @18
    vz
    @6
    vx
    vex
    #
    rankuni2
    vz
    vy
    @6
    @14
    @13
    crnk
    fvex
    dfiun2
    eqtri
    @17
    @9
    @16
    vy
    @9
    @16
    @13
    @6
    wcel
    #
    @15
    wa
    #
    vz
    wex
    #
    @12
    @9
    wcel
    #
    @15
    vz
    @6
    df-rex
    @22
    @14
    @9
    wcel
    #
    @15
    wa
    #
    vz
    wex
    #
    @23
    @21
    @25
    vz
    @20
    @24
    @15
    @13
    @6
    @19
    rankel
    anim1i
    eximi
    @23
    @15
    wa
    #
    vz
    wex
    @23
    @15
    vz
    wex
    #
    wa
    #
    @26
    @23
    @23
    @15
    vz
    19.42v
    @27
    @25
    vz
    @15
    @23
    @24
    @12
    @14
    @9
    eleq1
    pm5.32ri
    exbii
    @29
    @23
    @23
    @28
    simpl
    @23
    @28
    @23
    @12
    @12
    cr1
    cfv
    #
    crnk
    cfv
    #
    wceq
    #
    @28
    @23
    @31
    @12
    @23
    @12
    cr1
    cdm
    #
    wcel
    @31
    @12
    wceq
    @23
    @12
    con0
    @33
    @9
    @12
    @6
    rankon
    oneli
    cr1
    con0
    wfn
    @33
    con0
    wceq
    r1fnon
    con0
    cr1
    fndm
    ax-mp
    syl6eleqr
    @12
    rankr1id
    sylib
    eqcomd
    @15
    @32
    vz
    @30
    @12
    cr1
    fvex
    @13
    @30
    wceq
    @14
    @31
    @12
    @13
    @30
    crnk
    fveq2
    eqeq2d
    spcev
    syl
    ancli
    impbii
    3bitr3i
    sylib
    sylbi
    abssi
    unissi
    eqsstri
    @10
    @8
    csuc
    #
    cuni
    @8
    @9
    @34
    @9
    @7
    cpw
    #
    crnk
    cfv
    #
    @34
    @6
    @35
    wss
    @9
    @36
    wss
    @6
    pwuni
    @6
    @35
    @7
    vx
    vuniex
    #
    pwex
    rankss
    ax-mp
    @7
    @37
    rankpw
    sseqtri
    unissi
    @8
    @7
    rankon
    onunisuci
    sseqtri
    eqssi
    vtoclg
    @0
    wn
    #
    @2
    c0
    cuni
    #
    @4
    @38
    @2
    c0
    @39
    @0
    @1
    cvv
    wcel
    @2
    c0
    wceq
    cA
    uniexb
    @1
    crnk
    fvprc
    sylnbi
    uni0
    syl6eqr
    @38
    @3
    c0
    cA
    crnk
    fvprc
    unieqd
    eqtr4d
    pm2.61i
end
