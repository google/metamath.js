include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "cmbf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cioo.mm"
include "crn.mm"
include "wral.mm"
include "wa.mm"
include "cin.mm"
include "cnvresima.mm"
include "cnvi.mm"
include "imaeq1i.mm"
include "imai.mm"
include "eqtri.mm"
include "ineq1i.mm"
include "co.mm"
include "wceq.mm"
include "cxr.mm"
include "wrex.mm"
include "cxp.mm"
include "cr.mm"
include "cpw.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "ioof.mm"
include "ffn.mm"
include "ovelrn.mm"
include "mp2b.mm"
include "wi.mm"
include "id.mm"
include "ioombl.mm"
include "syl6eqel.mm"
include "a1i.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "inmbl.mm"
include "syl2anr.mm"
include "syl5eqel.mm"
include "ralrimiva.mm"
include "wss.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of.mm"
include "ax-mp.mm"
include "mblss.mm"
include "fss.mm"
include "sylancr.mm"
include "ismbf.mm"
include "syl.mm"
include "mpbird.mm"

theorem mbfid
  let cA: class A
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let vz: setvar z
  let cB: class B
  let cC: class C


  assert |- ( A e. dom vol -> ( _I |` A ) e. MblFn )

  proof
    cA
    cvol
    cdm
    #
    wcel
    #
    cid
    cA
    cres
    #
    cmbf
    wcel
    #
    @2
    ccnv
    vx
    cv
    #
    cima
    #
    @0
    wcel
    #
    vx
    cioo
    crn
    #
    wral
    #
    @1
    @6
    vx
    @7
    @1
    @4
    @7
    wcel
    #
    wa
    @5
    @4
    cA
    cin
    #
    @0
    @5
    cid
    ccnv
    #
    @4
    cima
    #
    cA
    cin
    @10
    cA
    @4
    cid
    cnvresima
    @12
    @4
    cA
    @12
    cid
    @4
    cima
    @4
    @11
    cid
    @4
    cnvi
    imaeq1i
    @4
    imai
    eqtri
    ineq1i
    eqtri
    @9
    @4
    @0
    wcel
    #
    @1
    @10
    @0
    wcel
    @1
    @9
    @4
    vy
    cv
    #
    vz
    cv
    #
    cioo
    co
    #
    wceq
    #
    vz
    cxr
    wrex
    vy
    cxr
    wrex
    #
    @13
    cxr
    cxr
    cxp
    #
    cr
    cpw
    #
    cioo
    wf
    cioo
    @19
    wfn
    @9
    @18
    wb
    ioof
    @19
    @20
    cioo
    ffn
    vy
    vz
    cxr
    cxr
    @4
    cioo
    ovelrn
    mp2b
    @17
    @13
    vy
    vz
    cxr
    cxr
    @17
    @13
    wi
    @14
    cxr
    wcel
    @15
    cxr
    wcel
    wa
    @17
    @4
    @16
    @0
    @17
    id
    @14
    @15
    ioombl
    syl6eqel
    a1i
    rexlimivv
    sylbi
    @1
    id
    @4
    cA
    inmbl
    syl2anr
    syl5eqel
    ralrimiva
    @1
    cA
    cr
    @2
    wf
    #
    @3
    @8
    wb
    @1
    cA
    cA
    @2
    wf
    #
    cA
    cr
    wss
    @21
    cA
    cA
    @2
    wf1o
    @22
    cA
    f1oi
    cA
    cA
    @2
    f1of
    ax-mp
    cA
    mblss
    cA
    cA
    cr
    @2
    fss
    sylancr
    vx
    cA
    @2
    ismbf
    syl
    mpbird
end
