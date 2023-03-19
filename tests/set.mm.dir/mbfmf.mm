include "cuni.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "cmbfm.mm"
include "wa.mm"
include "ismbfm.mm"
include "mpbid.mm"
include "simpld.mm"
include "elmapi.mm"
include "syl.mm"

theorem mbfmf
  let wph: wff ph
  let cS: class S
  let cT: class T
  let cF: class F
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  assume mbfmf.1: |- ( ph -> S e. U. ran sigAlgebra )
  assume mbfmf.2: |- ( ph -> T e. U. ran sigAlgebra )
  assume mbfmf.3: |- ( ph -> F e. ( S MblFnM T ) )


  assert |- ( ph -> F : U. S --> U. T )

  proof
    wph
    cF
    cT
    cuni
    #
    cS
    cuni
    #
    cmap
    co
    wcel
    #
    @1
    @0
    cF
    wf
    wph
    @2
    cF
    ccnv
    vx
    cv
    cima
    cS
    wcel
    vx
    cT
    wral
    #
    wph
    cF
    cS
    cT
    cmbfm
    co
    wcel
    @2
    @3
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
    simpld
    cF
    @0
    @1
    elmapi
    syl
end
