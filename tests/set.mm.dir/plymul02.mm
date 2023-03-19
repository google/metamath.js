include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
include "cc0.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "cmpt.mm"
include "c0p.mm"
include "cof.mm"
include "wa.mm"
include "plyf.mm"
include "ffvelrnda.mm"
include "mul02d.mm"
include "mpteq2dva.mm"
include "cvv.mm"
include "csn.mm"
include "wf.mm"
include "wfn.mm"
include "cxp.mm"
include "c0ex.mm"
include "fconst.mm"
include "df-0p.mm"
include "feq1i.mm"
include "mpbir.mm"
include "ffn.mm"
include "mp1i.mm"
include "syl.mm"
include "cnex.mm"
include "a1i.mm"
include "inidm.mm"
include "wceq.mm"
include "0pval.mm"
include "adantl.mm"
include "eqidd.mm"
include "offval.mm"
include "fconstmpt.mm"
include "eqtri.mm"
include "3eqtr4d.mm"

theorem plymul02
  let cS: class S
  let cF: class F
  let vx: setvar x


  assert |- ( F e. ( Poly ` S ) -> ( 0p oF x. F ) = 0p )

  proof
    cF
    cS
    cply
    cfv
    wcel
    #
    vx
    cc
    cc0
    vx
    cv
    #
    cF
    cfv
    #
    cmul
    co
    #
    cmpt
    vx
    cc
    cc0
    cmpt
    #
    c0p
    cF
    cmul
    cof
    co
    c0p
    @0
    vx
    cc
    @3
    cc0
    @0
    @1
    cc
    wcel
    #
    wa
    #
    @2
    @0
    cc
    cc
    @1
    cF
    cS
    cF
    plyf
    #
    ffvelrnda
    mul02d
    mpteq2dva
    @0
    vx
    cc
    cc
    cc0
    @2
    cmul
    cc
    c0p
    cF
    cvv
    cvv
    cc
    cc0
    csn
    #
    c0p
    wf
    #
    c0p
    cc
    wfn
    @0
    @9
    cc
    @8
    cc
    @8
    cxp
    #
    wf
    cc
    cc0
    c0ex
    fconst
    cc
    @8
    c0p
    @10
    df-0p
    feq1i
    mpbir
    cc
    @8
    c0p
    ffn
    mp1i
    @0
    cc
    cc
    cF
    wf
    cF
    cc
    wfn
    @7
    cc
    cc
    cF
    ffn
    syl
    cc
    cvv
    wcel
    @0
    cnex
    a1i
    #
    @11
    cc
    inidm
    @5
    @1
    c0p
    cfv
    cc0
    wceq
    @0
    @1
    0pval
    adantl
    @6
    @2
    eqidd
    offval
    c0p
    @4
    wceq
    @0
    c0p
    @10
    @4
    df-0p
    vx
    cc
    cc0
    fconstmpt
    eqtri
    a1i
    3eqtr4d
end
