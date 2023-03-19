include "cmbfm.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "csiga.mm"
include "wrex.mm"
include "cmap.mm"
include "ccnv.mm"
include "cima.mm"
include "wral.mm"
include "wa.mm"
include "cfv.mm"
include "cdm.mm"
include "cxp.mm"
include "wfun.mm"
include "wb.mm"
include "crab.mm"
include "df-mbfm.mm"
include "mpt2fun.mm"
include "elunirn.mm"
include "ax-mp.mm"
include "ovex.mm"
include "rabex.mm"
include "dmmpt2.mm"
include "rexeqi.mm"
include "cop.mm"
include "wceq.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "eleq2d.mm"
include "rexxp.mm"
include "3bitri.mm"
include "simpl.mm"
include "simpr.mm"
include "ismbfm.mm"
include "2rexbiia.mm"
include "bitri.mm"

theorem elunirnmbfm
  let vx: setvar x
  let vt: setvar t
  let cF: class F
  let vs: setvar s
  let vf: setvar f
  let va: setvar a

  disjoint s t
  disjoint F s
  disjoint F t
  disjoint s x
  disjoint t x
  disjoint F x
  disjoint f x
  disjoint a s
  disjoint a t
  disjoint F a
  disjoint f s
  disjoint f t
  assert |- ( F e. U. ran MblFnM <-> E. s e. U. ran sigAlgebra E. t e. U. ran sigAlgebra ( F e. ( U. t ^m U. s ) /\ A. x e. t ( `' F " x ) e. s ) )

  proof
    cF
    cmbfm
    crn
    cuni
    wcel
    #
    cF
    vs
    cv
    #
    vt
    cv
    #
    cmbfm
    co
    #
    wcel
    #
    vt
    csiga
    crn
    cuni
    #
    wrex
    vs
    @5
    wrex
    #
    cF
    @2
    cuni
    #
    @1
    cuni
    #
    cmap
    co
    #
    wcel
    cF
    ccnv
    vx
    cv
    #
    cima
    @1
    wcel
    vx
    @2
    wral
    wa
    #
    vt
    @5
    wrex
    vs
    @5
    wrex
    @0
    cF
    va
    cv
    #
    cmbfm
    cfv
    #
    wcel
    #
    va
    cmbfm
    cdm
    #
    wrex
    #
    @14
    va
    @5
    @5
    cxp
    #
    wrex
    @6
    cmbfm
    wfun
    @0
    @16
    wb
    vs
    vt
    @5
    @5
    vf
    cv
    ccnv
    @10
    cima
    @1
    wcel
    vx
    @2
    wral
    #
    vf
    @9
    crab
    #
    cmbfm
    vx
    vt
    vf
    vs
    df-mbfm
    #
    mpt2fun
    va
    cF
    cmbfm
    elunirn
    ax-mp
    @14
    va
    @15
    @17
    vs
    vt
    @5
    @5
    @19
    cmbfm
    @20
    @18
    vf
    @9
    @7
    @8
    cmap
    ovex
    rabex
    dmmpt2
    rexeqi
    @14
    @4
    va
    vs
    vt
    @5
    @5
    @12
    @1
    @2
    cop
    #
    wceq
    #
    @13
    @3
    cF
    @22
    @13
    @21
    cmbfm
    cfv
    @3
    @12
    @21
    cmbfm
    fveq2
    @1
    @2
    cmbfm
    df-ov
    syl6eqr
    eleq2d
    rexxp
    3bitri
    @4
    @11
    vs
    vt
    @5
    @5
    @1
    @5
    wcel
    #
    @2
    @5
    wcel
    #
    wa
    vx
    @1
    @2
    cF
    @23
    @24
    simpl
    @23
    @24
    simpr
    ismbfm
    2rexbiia
    bitri
end
