include "csur.mm"
include "wcel.mm"
include "cslt.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "cdm.mm"
include "wo.mm"
include "cun.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "c1o.mm"
include "c0.mm"
include "cop.mm"
include "c2o.mm"
include "ctp.mm"
include "sltval2.mm"
include "wceq.mm"
include "w3o.mm"
include "fvex.mm"
include "brtp.mm"
include "df-3or.mm"
include "ndmfv.mm"
include "1on.mm"
include "elexi.mm"
include "prid1.mm"
include "nosgnn0i.mm"
include "neeq1.mm"
include "mpbiri.mm"
include "neneqd.mm"
include "intnanrd.mm"
include "ioran.mm"
include "sylanbrc.mm"
include "syl.mm"
include "adantl.mm"
include "orel1.mm"
include "syl5bi.mm"
include "2on.mm"
include "prid2.mm"
include "con4i.mm"
include "syl6.mm"
include "ex.mm"
include "com23.mm"
include "sylbid.mm"
include "3impia.mm"
include "orrd.mm"
include "elun.mm"
include "sylibr.mm"

theorem nosepdmlem
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A e. No /\ B e. No /\ A <s B ) -> |^| { x e. On | ( A ` x ) =/= ( B ` x ) } e. ( dom A u. dom B ) )

  proof
    cA
    csur
    wcel
    #
    cB
    csur
    wcel
    #
    cA
    cB
    cslt
    wbr
    #
    w3a
    #
    vx
    cv
    #
    cA
    cfv
    @4
    cB
    cfv
    wne
    vx
    con0
    crab
    cint
    #
    cA
    cdm
    #
    wcel
    #
    @5
    cB
    cdm
    #
    wcel
    #
    wo
    @5
    @6
    @8
    cun
    wcel
    @3
    @7
    @9
    @0
    @1
    @2
    @7
    wn
    #
    @9
    wi
    #
    @0
    @1
    wa
    #
    @2
    @5
    cA
    cfv
    #
    @5
    cB
    cfv
    #
    c1o
    c0
    cop
    c1o
    c2o
    cop
    c0
    c2o
    cop
    ctp
    wbr
    #
    @11
    cA
    cB
    vx
    sltval2
    @15
    @13
    c1o
    wceq
    #
    @14
    c0
    wceq
    #
    wa
    #
    @16
    @14
    c2o
    wceq
    #
    wa
    #
    @13
    c0
    wceq
    #
    @19
    wa
    #
    w3o
    #
    @12
    @11
    c1o
    c0
    c1o
    c2o
    c0
    c2o
    @13
    @14
    @5
    cA
    fvex
    @5
    cB
    fvex
    brtp
    @12
    @10
    @23
    @9
    @12
    @10
    @23
    @9
    wi
    @12
    @10
    wa
    #
    @23
    @22
    @9
    @23
    @18
    @20
    wo
    #
    @22
    wo
    #
    @24
    @22
    @18
    @20
    @22
    df-3or
    @24
    @25
    wn
    #
    @26
    @22
    wi
    @10
    @27
    @12
    @10
    @21
    @27
    @5
    cA
    ndmfv
    @21
    @18
    wn
    @20
    wn
    @27
    @21
    @16
    @17
    @21
    @13
    c1o
    @21
    @13
    c1o
    wne
    c0
    c1o
    wne
    c1o
    c1o
    c2o
    c1o
    con0
    1on
    elexi
    prid1
    nosgnn0i
    @13
    c0
    c1o
    neeq1
    mpbiri
    neneqd
    #
    intnanrd
    @21
    @16
    @19
    @28
    intnanrd
    @18
    @20
    ioran
    sylanbrc
    syl
    adantl
    @25
    @22
    orel1
    syl
    syl5bi
    @19
    @9
    @21
    @9
    @19
    @9
    wn
    #
    @14
    c2o
    @29
    @17
    @14
    c2o
    wne
    #
    @5
    cB
    ndmfv
    @17
    @30
    c0
    c2o
    wne
    c2o
    c1o
    c2o
    c2o
    con0
    2on
    elexi
    prid2
    nosgnn0i
    @14
    c0
    c2o
    neeq1
    mpbiri
    syl
    neneqd
    con4i
    adantl
    syl6
    ex
    com23
    syl5bi
    sylbid
    3impia
    orrd
    @5
    @6
    @8
    elun
    sylibr
end
