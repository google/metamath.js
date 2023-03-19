include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cc.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "cr.mm"
include "cpm.mm"
include "co.mm"
include "cre.mm"
include "ccom.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cim.mm"
include "cioo.mm"
include "crn.mm"
include "wral.mm"
include "cmbf.mm"
include "wf.mm"
include "wss.mm"
include "simplr.mm"
include "fconstmpt.mm"
include "fmptd.mm"
include "mblss.mm"
include "adantr.mm"
include "cvv.mm"
include "cnex.mm"
include "reex.mm"
include "elpm2r.mm"
include "mpanl12.mm"
include "syl2anc.mm"
include "cfv.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "ref.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "syl6eqr.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "recl.mm"
include "mbfconstlem.mm"
include "sylan2.mm"
include "eqeltrd.mm"
include "imf.mm"
include "imcl.mm"
include "jca.mm"
include "ralrimivw.mm"
include "ismbf1.mm"
include "sylanbrc.mm"

theorem mbfconst
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let vz: setvar z
  let cC: class C


  assert |- ( ( A e. dom vol /\ B e. CC ) -> ( A X. { B } ) e. MblFn )

  proof
    cA
    cvol
    cdm
    #
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    cB
    csn
    cxp
    #
    cc
    cr
    cpm
    co
    wcel
    #
    cre
    @4
    ccom
    #
    ccnv
    #
    vy
    cv
    #
    cima
    #
    @0
    wcel
    #
    cim
    @4
    ccom
    #
    ccnv
    #
    @8
    cima
    #
    @0
    wcel
    #
    wa
    #
    vy
    cioo
    crn
    #
    wral
    @4
    cmbf
    wcel
    @3
    cA
    cc
    @4
    wf
    #
    cA
    cr
    wss
    #
    @5
    @3
    vx
    cA
    cB
    cc
    @4
    @1
    @2
    vx
    cv
    cA
    wcel
    simplr
    #
    vx
    cA
    cB
    fconstmpt
    #
    fmptd
    @1
    @18
    @2
    cA
    mblss
    adantr
    cc
    cvv
    wcel
    cr
    cvv
    wcel
    @17
    @18
    wa
    @5
    cnex
    reex
    cc
    cr
    cA
    @4
    cvv
    cvv
    elpm2r
    mpanl12
    syl2anc
    @3
    @15
    vy
    @16
    @3
    @10
    @14
    @3
    @9
    cA
    cB
    cre
    cfv
    #
    csn
    cxp
    #
    ccnv
    #
    @8
    cima
    #
    @0
    @3
    @7
    @23
    @8
    @3
    @6
    @22
    @3
    @6
    vx
    cA
    @21
    cmpt
    @22
    @3
    vx
    vy
    cA
    cc
    cB
    @8
    cre
    cfv
    @21
    @4
    cre
    @19
    @4
    vx
    cA
    cB
    cmpt
    wceq
    @3
    @20
    a1i
    #
    @3
    vy
    cc
    cr
    cre
    cc
    cr
    cre
    wf
    @3
    ref
    a1i
    feqmptd
    @8
    cB
    cre
    fveq2
    fmptco
    vx
    cA
    @21
    fconstmpt
    syl6eqr
    cnveqd
    imaeq1d
    @2
    @1
    @21
    cr
    wcel
    @24
    @0
    wcel
    cB
    recl
    cA
    @8
    @21
    mbfconstlem
    sylan2
    eqeltrd
    @3
    @13
    cA
    cB
    cim
    cfv
    #
    csn
    cxp
    #
    ccnv
    #
    @8
    cima
    #
    @0
    @3
    @12
    @28
    @8
    @3
    @11
    @27
    @3
    @11
    vx
    cA
    @26
    cmpt
    @27
    @3
    vx
    vy
    cA
    cc
    cB
    @8
    cim
    cfv
    @26
    @4
    cim
    @19
    @25
    @3
    vy
    cc
    cr
    cim
    cc
    cr
    cim
    wf
    @3
    imf
    a1i
    feqmptd
    @8
    cB
    cim
    fveq2
    fmptco
    vx
    cA
    @26
    fconstmpt
    syl6eqr
    cnveqd
    imaeq1d
    @2
    @1
    @26
    cr
    wcel
    @29
    @0
    wcel
    cB
    imcl
    cA
    @8
    @26
    mbfconstlem
    sylan2
    eqeltrd
    jca
    ralrimivw
    vy
    @4
    ismbf1
    sylanbrc
end
