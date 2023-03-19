include "cv.mm"
include "com.mm"
include "wcel.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "cfv.mm"
include "c0.mm"
include "csuc.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "cint.mm"
include "con0.mm"
include "wne.mm"
include "omsson.mm"
include "sstr.mm"
include "mpan2.mm"
include "wex.mm"
include "wi.mm"
include "peano1.mm"
include "eleq1.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "ax-mp.mm"
include "df-rex.mm"
include "sylib.mm"
include "exsimpl.mm"
include "syl.mm"
include "n0.mm"
include "sylibr.mm"
include "onint.mm"
include "syl2an.mm"
include "cvv.mm"
include "cdif.mm"
include "cmpt.mm"
include "crdg.mm"
include "cres.mm"
include "fveq1i.mm"
include "fr0g.mm"
include "syl5req.mm"
include "ibi.mm"
include "unblem1.mm"
include "wb.mm"
include "suceq.mm"
include "difeq2d.mm"
include "inteqd.mm"
include "frsucmpt2.mm"
include "eqcomd.mm"
include "ex.mm"
include "ibd.mm"
include "syl5.mm"
include "expd.mm"
include "finds2.mm"
include "com12.mm"

theorem unblem2
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cF: class F
  let vu: setvar u
  let vy: setvar y
  assume unblem.2: |- F = ( rec ( ( x e. _V |-> |^| ( A \ suc x ) ) , |^| A ) |` _om )

  disjoint v w
  disjoint v x
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint F v
  disjoint F w
  disjoint F z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v y
  disjoint w y
  disjoint x y
  disjoint y z
  disjoint A y
  disjoint F u
  disjoint F y
  assert |- ( ( A C_ _om /\ A. w e. _om E. v e. A w e. v ) -> ( z e. _om -> ( F ` z ) e. A ) )

  proof
    vz
    cv
    #
    com
    wcel
    cA
    com
    wss
    #
    vw
    cv
    #
    vv
    cv
    #
    wcel
    #
    vv
    cA
    wrex
    #
    vw
    com
    wral
    #
    wa
    #
    @0
    cF
    cfv
    #
    cA
    wcel
    #
    @9
    c0
    cF
    cfv
    #
    cA
    wcel
    #
    vu
    cv
    #
    cF
    cfv
    #
    cA
    wcel
    #
    @12
    csuc
    #
    cF
    cfv
    #
    cA
    wcel
    #
    @7
    vz
    vu
    @0
    c0
    wceq
    @8
    @10
    cA
    @0
    c0
    cF
    fveq2
    eleq1d
    @0
    @12
    wceq
    @8
    @13
    cA
    @0
    @12
    cF
    fveq2
    eleq1d
    @0
    @15
    wceq
    @8
    @16
    cA
    @0
    @15
    cF
    fveq2
    eleq1d
    @7
    cA
    cint
    #
    cA
    wcel
    #
    @11
    @1
    cA
    con0
    wss
    #
    cA
    c0
    wne
    #
    @19
    @6
    @1
    com
    con0
    wss
    @20
    omsson
    cA
    com
    con0
    sstr
    mpan2
    @6
    @3
    cA
    wcel
    #
    vv
    wex
    #
    @21
    @6
    @22
    c0
    @3
    wcel
    #
    wa
    vv
    wex
    #
    @23
    @6
    @24
    vv
    cA
    wrex
    #
    @25
    c0
    com
    wcel
    @6
    @26
    wi
    peano1
    @5
    @26
    vw
    c0
    com
    @2
    c0
    wceq
    @4
    @24
    vv
    cA
    @2
    c0
    @3
    eleq1
    rexbidv
    rspcv
    ax-mp
    @24
    vv
    cA
    df-rex
    sylib
    @22
    @24
    vv
    exsimpl
    syl
    vv
    cA
    n0
    sylibr
    cA
    onint
    syl2an
    @19
    @11
    @19
    @18
    @10
    cA
    @19
    @10
    c0
    vx
    cvv
    cA
    vx
    cv
    #
    csuc
    #
    cdif
    #
    cint
    #
    cmpt
    #
    @18
    crdg
    com
    cres
    #
    cfv
    @18
    c0
    cF
    @32
    unblem.2
    fveq1i
    @18
    cA
    @31
    fr0g
    syl5req
    eleq1d
    ibi
    syl
    @12
    com
    wcel
    #
    @7
    @14
    @17
    @7
    @14
    wa
    cA
    @13
    csuc
    #
    cdif
    #
    cint
    #
    cA
    wcel
    #
    @33
    @17
    vw
    vv
    @13
    cA
    unblem1
    @33
    @37
    @17
    @33
    @37
    @37
    @17
    wb
    @33
    @37
    wa
    #
    @36
    @16
    cA
    @38
    @16
    @36
    vx
    vy
    @18
    @12
    @30
    @36
    cA
    vy
    cv
    #
    csuc
    #
    cdif
    #
    cint
    cF
    cA
    unblem.2
    @39
    @27
    wceq
    #
    @41
    @29
    @42
    @40
    @28
    cA
    @39
    @27
    suceq
    difeq2d
    inteqd
    @39
    @13
    wceq
    #
    @41
    @35
    @43
    @40
    @34
    cA
    @39
    @13
    suceq
    difeq2d
    inteqd
    frsucmpt2
    eqcomd
    eleq1d
    ex
    ibd
    syl5
    expd
    finds2
    com12
end
