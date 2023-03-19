include "cr.mm"
include "wf.mm"
include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cmbf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cioo.mm"
include "crn.mm"
include "wral.mm"
include "mbfdm.mm"
include "fdm.mm"
include "eleq1d.mm"
include "syl5ib.mm"
include "wi.mm"
include "cmnf.mm"
include "cpnf.mm"
include "co.mm"
include "ioomax.mm"
include "ioorebas.mm"
include "eqeltrri.mm"
include "wceq.mm"
include "imaeq2.mm"
include "rspcv.mm"
include "ax-mp.mm"
include "fimacnv.mm"
include "wb.mm"
include "wa.mm"
include "cc.mm"
include "cpm.mm"
include "cre.mm"
include "ccom.mm"
include "cim.mm"
include "cfv.mm"
include "cmpt.mm"
include "ffvelrn.mm"
include "adantlr.mm"
include "rered.mm"
include "mpteq2dva.mm"
include "recnd.mm"
include "simpl.mm"
include "feqmptd.mm"
include "ref.mm"
include "a1i.mm"
include "fveq2.mm"
include "fmptco.mm"
include "3eqtr4rd.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "imf.mm"
include "reim0d.mm"
include "eqtrd.mm"
include "fconstmpt.mm"
include "syl6eqr.mm"
include "simpr.mm"
include "0re.mm"
include "mbfconstlem.mm"
include "sylancl.mm"
include "eqeltrd.mm"
include "biantrud.mm"
include "bitrd.mm"
include "ralbidv.mm"
include "wss.mm"
include "ax-resscn.mm"
include "fss.mm"
include "mpan2.mm"
include "mblss.mm"
include "cvv.mm"
include "cnex.mm"
include "reex.mm"
include "elpm2r.mm"
include "mpanl12.mm"
include "syl2an.mm"
include "biantrurd.mm"
include "ismbf1.mm"
include "syl6rbbr.mm"
include "ex.mm"
include "pm5.21ndd.mm"

theorem ismbf
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vf: setvar f
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C

  disjoint F x
  disjoint A x
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint x y
  disjoint F y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint C x
  assert |- ( F : A --> RR -> ( F e. MblFn <-> A. x e. ran (,) ( `' F " x ) e. dom vol ) )

  proof
    cA
    cr
    cF
    wf
    #
    cA
    cvol
    cdm
    #
    wcel
    #
    cF
    cmbf
    wcel
    #
    cF
    ccnv
    #
    vx
    cv
    #
    cima
    #
    @1
    wcel
    #
    vx
    cioo
    crn
    #
    wral
    #
    @3
    cF
    cdm
    #
    @1
    wcel
    @0
    @2
    cF
    mbfdm
    @0
    @10
    cA
    @1
    cA
    cr
    cF
    fdm
    eleq1d
    syl5ib
    @9
    @4
    cr
    cima
    #
    @1
    wcel
    #
    @0
    @2
    cr
    @8
    wcel
    @9
    @12
    wi
    cmnf
    cpnf
    cioo
    co
    cr
    @8
    ioomax
    cmnf
    cpnf
    ioorebas
    eqeltrri
    @7
    @12
    vx
    cr
    @8
    @5
    cr
    wceq
    @6
    @11
    @1
    @5
    cr
    @4
    imaeq2
    eleq1d
    rspcv
    ax-mp
    @0
    @11
    cA
    @1
    cA
    cr
    cF
    fimacnv
    eleq1d
    syl5ib
    @0
    @2
    @3
    @9
    wb
    @0
    @2
    wa
    #
    @9
    cF
    cc
    cr
    cpm
    co
    wcel
    #
    cre
    cF
    ccom
    #
    ccnv
    #
    @5
    cima
    #
    @1
    wcel
    #
    cim
    cF
    ccom
    #
    ccnv
    #
    @5
    cima
    #
    @1
    wcel
    #
    wa
    #
    vx
    @8
    wral
    #
    wa
    #
    @3
    @13
    @9
    @24
    @25
    @13
    @7
    @23
    vx
    @8
    @13
    @7
    @18
    @23
    @13
    @6
    @17
    @1
    @13
    @4
    @16
    @5
    @13
    cF
    @15
    @13
    vx
    cA
    @5
    cF
    cfv
    #
    cre
    cfv
    #
    cmpt
    vx
    cA
    @26
    cmpt
    @15
    cF
    @13
    vx
    cA
    @27
    @26
    @13
    @5
    cA
    wcel
    #
    wa
    #
    @26
    @0
    @28
    @26
    cr
    wcel
    @2
    cA
    cr
    @5
    cF
    ffvelrn
    adantlr
    #
    rered
    mpteq2dva
    @13
    vx
    vy
    cA
    cc
    @26
    vy
    cv
    #
    cre
    cfv
    @27
    cF
    cre
    @29
    @26
    @30
    recnd
    #
    @13
    vx
    cA
    cr
    cF
    @0
    @2
    simpl
    feqmptd
    #
    @13
    vy
    cc
    cr
    cre
    cc
    cr
    cre
    wf
    @13
    ref
    a1i
    feqmptd
    @31
    @26
    cre
    fveq2
    fmptco
    @33
    3eqtr4rd
    cnveqd
    imaeq1d
    eleq1d
    @13
    @22
    @18
    @13
    @21
    cA
    cc0
    csn
    cxp
    #
    ccnv
    #
    @5
    cima
    #
    @1
    @13
    @20
    @35
    @5
    @13
    @19
    @34
    @13
    @19
    vx
    cA
    cc0
    cmpt
    #
    @34
    @13
    @19
    vx
    cA
    @26
    cim
    cfv
    #
    cmpt
    @37
    @13
    vx
    vy
    cA
    cc
    @26
    @31
    cim
    cfv
    @38
    cF
    cim
    @32
    @33
    @13
    vy
    cc
    cr
    cim
    cc
    cr
    cim
    wf
    @13
    imf
    a1i
    feqmptd
    @31
    @26
    cim
    fveq2
    fmptco
    @13
    vx
    cA
    @38
    cc0
    @29
    @26
    @30
    reim0d
    mpteq2dva
    eqtrd
    vx
    cA
    cc0
    fconstmpt
    syl6eqr
    cnveqd
    imaeq1d
    @13
    @2
    cc0
    cr
    wcel
    @36
    @1
    wcel
    @0
    @2
    simpr
    0re
    cA
    @5
    cc0
    mbfconstlem
    sylancl
    eqeltrd
    biantrud
    bitrd
    ralbidv
    @13
    @14
    @24
    @0
    cA
    cc
    cF
    wf
    #
    cA
    cr
    wss
    #
    @14
    @2
    @0
    cr
    cc
    wss
    @39
    ax-resscn
    cA
    cr
    cc
    cF
    fss
    mpan2
    cA
    mblss
    cc
    cvv
    wcel
    cr
    cvv
    wcel
    @39
    @40
    wa
    @14
    cnex
    reex
    cc
    cr
    cA
    cF
    cvv
    cvv
    elpm2r
    mpanl12
    syl2an
    biantrurd
    bitrd
    vx
    cF
    ismbf1
    syl6rbbr
    ex
    pm5.21ndd
end
