include "cop.mm"
include "csn.mm"
include "snex.mm"
include "cxp.mm"
include "wf.mm"
include "wf1o.mm"
include "opex.mm"
include "f1osn.mm"
include "f1of.mm"
include "ax-mp.mm"
include "xpsn.mm"
include "feq2i.mm"
include "mpbir.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "co.mm"
include "velsn.mm"
include "w3a.mm"
include "wa.mm"
include "oveq2.mm"
include "oveq1.mm"
include "cfv.mm"
include "df-ov.mm"
include "fvsn.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "sylan9eq.mm"
include "oveq1d.mm"
include "sylan9eqr.mm"
include "3impa.mm"
include "oveq2d.mm"
include "3impb.mm"
include "eqtr4d.mm"
include "syl3anb.mm"
include "snid.mm"
include "id.mm"
include "sylbi.mm"
include "a1i.mm"
include "isgrpoi.mm"

theorem grposnOLD
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume grposnOLD.1: |- A e. _V


  assert |- { <. <. A , A >. , A >. } e. GrpOp

  proof
    vx
    vy
    vz
    cA
    cA
    cA
    cop
    #
    cA
    cop
    csn
    #
    cA
    cA
    csn
    #
    cA
    snex
    @2
    @2
    cxp
    #
    @2
    @1
    wf
    @0
    csn
    #
    @2
    @1
    wf
    #
    @4
    @2
    @1
    wf1o
    @5
    @0
    cA
    cA
    cA
    opex
    #
    grposnOLD.1
    f1osn
    @4
    @2
    @1
    f1of
    ax-mp
    @3
    @4
    @2
    @1
    cA
    cA
    grposnOLD.1
    grposnOLD.1
    xpsn
    feq2i
    mpbir
    vx
    cv
    #
    @2
    wcel
    #
    @7
    cA
    wceq
    #
    vy
    cv
    #
    @2
    wcel
    @10
    cA
    wceq
    #
    vz
    cv
    #
    @2
    wcel
    @12
    cA
    wceq
    #
    @7
    @10
    @1
    co
    #
    @12
    @1
    co
    #
    @7
    @10
    @12
    @1
    co
    #
    @1
    co
    #
    wceq
    vx
    cA
    velsn
    #
    vy
    cA
    velsn
    vz
    cA
    velsn
    @9
    @11
    @13
    w3a
    @15
    cA
    @17
    @9
    @11
    @13
    @15
    cA
    wceq
    @13
    @9
    @11
    wa
    #
    @15
    @14
    cA
    @1
    co
    #
    cA
    @12
    cA
    @14
    @1
    oveq2
    @19
    @20
    cA
    cA
    @1
    co
    #
    cA
    @19
    @14
    cA
    cA
    @1
    @9
    @11
    @14
    cA
    @10
    @1
    co
    #
    cA
    @7
    cA
    @10
    @1
    oveq1
    @11
    @22
    @21
    cA
    @10
    cA
    cA
    @1
    oveq2
    @21
    @0
    @1
    cfv
    cA
    cA
    cA
    @1
    df-ov
    @0
    cA
    @6
    grposnOLD.1
    fvsn
    eqtri
    #
    syl6eq
    sylan9eq
    oveq1d
    @23
    syl6eq
    sylan9eqr
    3impa
    @9
    @11
    @13
    @17
    cA
    wceq
    @9
    @11
    @13
    wa
    #
    @17
    cA
    @16
    @1
    co
    #
    cA
    @7
    cA
    @16
    @1
    oveq1
    @24
    @25
    @21
    cA
    @24
    @16
    cA
    cA
    @1
    @11
    @13
    @16
    cA
    @12
    @1
    co
    #
    cA
    @10
    cA
    @12
    @1
    oveq1
    @13
    @26
    @21
    cA
    @12
    cA
    cA
    @1
    oveq2
    @23
    syl6eq
    sylan9eq
    oveq2d
    @23
    syl6eq
    sylan9eq
    3impb
    eqtr4d
    syl3anb
    cA
    grposnOLD.1
    snid
    #
    @8
    @9
    cA
    @7
    @1
    co
    #
    @7
    wceq
    @18
    @9
    @28
    cA
    @7
    @9
    @28
    @21
    cA
    @7
    cA
    cA
    @1
    oveq2
    @23
    syl6eq
    #
    @9
    id
    eqtr4d
    sylbi
    cA
    @2
    wcel
    @8
    @27
    a1i
    @8
    @9
    @28
    cA
    wceq
    @18
    @29
    sylbi
    isgrpoi
end
