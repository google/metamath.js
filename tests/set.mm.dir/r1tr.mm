include "cr1.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "wtr.mm"
include "con0.mm"
include "wlim.mm"
include "word.mm"
include "wss.mm"
include "wfun.mm"
include "r1funlim.mm"
include "simpri.mm"
include "limord.mm"
include "ordsson.mm"
include "mp2b.mm"
include "sseli.mm"
include "cv.mm"
include "c0.mm"
include "csuc.mm"
include "wceq.mm"
include "wb.mm"
include "fveq2.mm"
include "r10.mm"
include "syl6eq.mm"
include "treq.mm"
include "syl.mm"
include "tr0.mm"
include "wa.mm"
include "limsuc.mm"
include "ax-mp.mm"
include "cpw.mm"
include "simpr.mm"
include "pwtr.mm"
include "sylib.mm"
include "r1sucg.mm"
include "syl5ibrcom.mm"
include "syl5bir.mm"
include "wn.mm"
include "ndmfv.mm"
include "mpbiri.mm"
include "pm2.61d1.mm"
include "ex.mm"
include "wral.mm"
include "ciun.mm"
include "triun.mm"
include "r1limg.mm"
include "ancoms.mm"
include "syl5ibr.mm"
include "impancom.mm"
include "tfinds.mm"
include "pm2.61i.mm"

theorem r1tr
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- Tr ( R1 ` A )

  proof
    cA
    cr1
    cdm
    #
    wcel
    #
    cA
    cr1
    cfv
    #
    wtr
    #
    @1
    cA
    con0
    wcel
    @3
    @0
    con0
    cA
    @0
    wlim
    #
    @0
    word
    @0
    con0
    wss
    cr1
    wfun
    @4
    r1funlim
    simpri
    #
    @0
    limord
    @0
    ordsson
    mp2b
    sseli
    vx
    cv
    #
    cr1
    cfv
    #
    wtr
    #
    c0
    wtr
    #
    vy
    cv
    #
    cr1
    cfv
    #
    wtr
    #
    @10
    csuc
    #
    cr1
    cfv
    #
    wtr
    #
    @3
    vx
    vy
    cA
    @6
    c0
    wceq
    #
    @7
    c0
    wceq
    #
    @8
    @9
    wb
    #
    @16
    @7
    c0
    cr1
    cfv
    c0
    @6
    c0
    cr1
    fveq2
    r10
    syl6eq
    @7
    c0
    treq
    #
    syl
    @6
    @10
    wceq
    @7
    @11
    wceq
    @8
    @12
    wb
    @6
    @10
    cr1
    fveq2
    @7
    @11
    treq
    syl
    @6
    @13
    wceq
    @7
    @14
    wceq
    @8
    @15
    wb
    @6
    @13
    cr1
    fveq2
    @7
    @14
    treq
    syl
    @6
    cA
    wceq
    @7
    @2
    wceq
    @8
    @3
    wb
    @6
    cA
    cr1
    fveq2
    @7
    @2
    treq
    syl
    tr0
    @10
    con0
    wcel
    #
    @12
    @15
    @20
    @12
    wa
    #
    @13
    @0
    wcel
    #
    @15
    @22
    @10
    @0
    wcel
    #
    @21
    @15
    @4
    @23
    @22
    wb
    @5
    @0
    @10
    limsuc
    ax-mp
    @21
    @15
    @23
    @11
    cpw
    #
    wtr
    #
    @21
    @12
    @25
    @20
    @12
    simpr
    @11
    pwtr
    sylib
    @23
    @14
    @24
    wceq
    @15
    @25
    wb
    @10
    r1sucg
    @14
    @24
    treq
    syl
    syl5ibrcom
    syl5bir
    @22
    wn
    #
    @15
    @9
    tr0
    @26
    @14
    c0
    wceq
    @15
    @9
    wb
    @13
    cr1
    ndmfv
    @14
    c0
    treq
    syl
    mpbiri
    pm2.61d1
    ex
    @6
    wlim
    #
    @12
    vy
    @6
    wral
    #
    @8
    @27
    @28
    wa
    @6
    @0
    wcel
    #
    @8
    @27
    @29
    @28
    @8
    @28
    @8
    @27
    @29
    wa
    #
    vy
    @6
    @11
    ciun
    #
    wtr
    #
    vy
    @6
    @11
    triun
    @30
    @7
    @31
    wceq
    #
    @8
    @32
    wb
    @29
    @27
    @33
    vy
    @6
    r1limg
    ancoms
    @7
    @31
    treq
    syl
    syl5ibr
    impancom
    @29
    wn
    #
    @8
    @9
    tr0
    @34
    @17
    @18
    @6
    cr1
    ndmfv
    @19
    syl
    mpbiri
    pm2.61d1
    ex
    tfinds
    syl
    @1
    wn
    #
    @3
    @9
    tr0
    @35
    @2
    c0
    wceq
    @3
    @9
    wb
    cA
    cr1
    ndmfv
    @2
    c0
    treq
    syl
    mpbiri
    pm2.61i
end
