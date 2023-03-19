include "wcel.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "cuni.mm"
include "cmap.mm"
include "co.mm"
include "cmbfm.mm"
include "wa.mm"
include "ismbfm.mm"
include "mpbid.mm"
include "simprd.mm"
include "wceq.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"

theorem mbfmcnvima
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cT: class T
  let cF: class F
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  assume mbfmf.1: |- ( ph -> S e. U. ran sigAlgebra )
  assume mbfmf.2: |- ( ph -> T e. U. ran sigAlgebra )
  assume mbfmf.3: |- ( ph -> F e. ( S MblFnM T ) )
  assume mbfmcnvima.4: |- ( ph -> A e. T )


  assert |- ( ph -> ( `' F " A ) e. S )

  proof
    wph
    cA
    cT
    wcel
    cF
    ccnv
    #
    vx
    cv
    #
    cima
    #
    cS
    wcel
    #
    vx
    cT
    wral
    #
    @0
    cA
    cima
    #
    cS
    wcel
    #
    mbfmcnvima.4
    wph
    cF
    cT
    cuni
    cS
    cuni
    cmap
    co
    wcel
    #
    @4
    wph
    cF
    cS
    cT
    cmbfm
    co
    wcel
    @7
    @4
    wa
    mbfmf.3
    wph
    vx
    cS
    cT
    cF
    mbfmf.1
    mbfmf.2
    ismbfm
    mpbid
    simprd
    @3
    @6
    vx
    cA
    cT
    @1
    cA
    wceq
    @2
    @5
    cS
    @1
    cA
    @0
    imaeq2
    eleq1d
    rspcv
    sylc
end
