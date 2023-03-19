include "c1.mm"
include "wcel.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "cn.mm"
include "cvv.mm"
include "cmpt.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "crn.mm"
include "cima.mm"
include "df-nn.mm"
include "df-ima.mm"
include "eqtri.mm"
include "wf.mm"
include "wss.mm"
include "wfn.mm"
include "cfv.mm"
include "frfnom.mm"
include "a1i.mm"
include "c0.mm"
include "csuc.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "cc.mm"
include "ax-1cn.mm"
include "fr0g.mm"
include "ax-mp.mm"
include "simpl.mm"
include "syl5eqel.mm"
include "wi.mm"
include "oveq1.mm"
include "rspccv.mm"
include "ad2antlr.mm"
include "wb.mm"
include "ovex.mm"
include "eqid.mm"
include "frsucmpt2.mm"
include "mpan2.mm"
include "adantl.mm"
include "sylibrd.mm"
include "expcom.mm"
include "finds2.mm"
include "com12.mm"
include "ralrimiv.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "frn.mm"
include "syl.mm"
include "syl5eqss.mm"

theorem peano5nni
  let vx: setvar x
  let cA: class A
  let vn: setvar n
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( ( 1 e. A /\ A. x e. A ( x + 1 ) e. A ) -> NN C_ A )

  proof
    c1
    cA
    wcel
    #
    vx
    cv
    #
    c1
    caddc
    co
    #
    cA
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    cn
    vn
    cvv
    vn
    cv
    #
    c1
    caddc
    co
    #
    cmpt
    #
    c1
    crdg
    #
    com
    cres
    #
    crn
    #
    cA
    cn
    @9
    com
    cima
    @11
    vn
    df-nn
    @9
    com
    df-ima
    eqtri
    @5
    com
    cA
    @10
    wf
    #
    @11
    cA
    wss
    @5
    @10
    com
    wfn
    #
    vy
    cv
    #
    @10
    cfv
    #
    cA
    wcel
    #
    vy
    com
    wral
    @12
    @13
    @5
    c1
    @8
    frfnom
    a1i
    @5
    @16
    vy
    com
    @14
    com
    wcel
    @5
    @16
    @16
    c0
    @10
    cfv
    #
    cA
    wcel
    vz
    cv
    #
    @10
    cfv
    #
    cA
    wcel
    #
    @18
    csuc
    #
    @10
    cfv
    #
    cA
    wcel
    #
    @5
    vy
    vz
    @14
    c0
    wceq
    @15
    @17
    cA
    @14
    c0
    @10
    fveq2
    eleq1d
    @14
    @18
    wceq
    @15
    @19
    cA
    @14
    @18
    @10
    fveq2
    eleq1d
    @14
    @21
    wceq
    @15
    @22
    cA
    @14
    @21
    @10
    fveq2
    eleq1d
    @5
    @17
    c1
    cA
    c1
    cc
    wcel
    @17
    c1
    wceq
    ax-1cn
    c1
    cc
    @8
    fr0g
    ax-mp
    @0
    @4
    simpl
    syl5eqel
    @5
    @18
    com
    wcel
    #
    @20
    @23
    wi
    @5
    @24
    wa
    @20
    @19
    c1
    caddc
    co
    #
    cA
    wcel
    #
    @23
    @4
    @20
    @26
    wi
    @0
    @24
    @3
    @26
    vx
    @19
    cA
    @1
    @19
    wceq
    @2
    @25
    cA
    @1
    @19
    c1
    caddc
    oveq1
    eleq1d
    rspccv
    ad2antlr
    @24
    @23
    @26
    wb
    @5
    @24
    @22
    @25
    cA
    @24
    @25
    cvv
    wcel
    @22
    @25
    wceq
    @19
    c1
    caddc
    ovex
    vn
    vy
    c1
    @18
    @7
    @25
    @14
    c1
    caddc
    co
    @10
    cvv
    @10
    eqid
    @14
    @6
    c1
    caddc
    oveq1
    @14
    @19
    c1
    caddc
    oveq1
    frsucmpt2
    mpan2
    eleq1d
    adantl
    sylibrd
    expcom
    finds2
    com12
    ralrimiv
    vy
    com
    cA
    @10
    ffnfv
    sylanbrc
    com
    cA
    @10
    frn
    syl
    syl5eqss
end
