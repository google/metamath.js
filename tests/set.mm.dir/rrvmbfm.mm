include "crrv.mm"
include "cfv.mm"
include "cdm.mm"
include "cbrsiga.mm"
include "cmbfm.mm"
include "co.mm"
include "cprb.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "dmeq.mm"
include "oveq1d.mm"
include "df-rrv.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "eleq2d.mm"

theorem rrvmbfm
  let wph: wff ph
  let cP: class P
  let cX: class X
  let vp: setvar p
  let vy: setvar y
  assume isrrvv.1: |- ( ph -> P e. Prob )


  assert |- ( ph -> ( X e. ( rRndVar ` P ) <-> X e. ( dom P MblFnM BrSiga ) ) )

  proof
    wph
    cP
    crrv
    cfv
    #
    cP
    cdm
    #
    cbrsiga
    cmbfm
    co
    #
    cX
    wph
    cP
    cprb
    wcel
    @0
    @2
    wceq
    isrrvv.1
    vp
    cP
    vp
    cv
    #
    cdm
    #
    cbrsiga
    cmbfm
    co
    @2
    cprb
    crrv
    @3
    cP
    wceq
    @4
    @1
    cbrsiga
    cmbfm
    @3
    cP
    dmeq
    oveq1d
    vp
    df-rrv
    @1
    cbrsiga
    cmbfm
    ovex
    fvmpt
    syl
    eleq2d
end
