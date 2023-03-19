include "cv.mm"
include "cdm.mm"
include "cuni.mm"
include "wcel.mm"
include "wa.mm"
include "corvc.mm"
include "co.mm"
include "cfv.mm"
include "wbr.mm"
include "wb.mm"
include "rrvdm.mm"
include "eleq2d.mm"
include "biimprd.mm"
include "imdistani.mm"
include "crrv.mm"
include "wfn.mm"
include "wfun.mm"
include "rrvfn.mm"
include "fnfun.mm"
include "syl.mm"
include "elorvc.mm"

theorem elorrvc
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cP: class P
  let cR: class R
  let cV: class V
  let cX: class X
  assume orrvccel.1: |- ( ph -> P e. Prob )
  assume orrvccel.2: |- ( ph -> X e. ( rRndVar ` P ) )
  assume orrvccel.4: |- ( ph -> A e. V )

  disjoint A z
  disjoint R z
  disjoint X z
  assert |- ( ( ph /\ z e. U. dom P ) -> ( z e. ( X oRVC R A ) <-> ( X ` z ) R A ) )

  proof
    wph
    vz
    cv
    #
    cP
    cdm
    cuni
    #
    wcel
    #
    wa
    wph
    @0
    cX
    cdm
    #
    wcel
    #
    wa
    @0
    cX
    cA
    cR
    corvc
    co
    wcel
    @0
    cX
    cfv
    cA
    cR
    wbr
    wb
    wph
    @2
    @4
    wph
    @4
    @2
    wph
    @3
    @1
    @0
    wph
    cP
    cX
    orrvccel.1
    orrvccel.2
    rrvdm
    eleq2d
    biimprd
    imdistani
    wph
    vz
    cA
    cR
    cP
    crrv
    cfv
    cV
    cX
    wph
    cX
    @1
    wfn
    cX
    wfun
    wph
    cP
    cX
    orrvccel.1
    orrvccel.2
    rrvfn
    @1
    cX
    fnfun
    syl
    orrvccel.2
    orrvccel.4
    elorvc
    syl
end
