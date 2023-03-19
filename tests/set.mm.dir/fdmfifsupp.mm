include "cfsupp.mm"
include "wbr.mm"
include "wfun.mm"
include "csupp.mm"
include "co.mm"
include "cfn.mm"
include "wcel.mm"
include "wf.mm"
include "ffun.mm"
include "syl.mm"
include "fdmfisuppfi.mm"
include "cvv.mm"
include "wa.mm"
include "wb.mm"
include "wfn.mm"
include "ffn.mm"
include "fnex.mm"
include "syl2anc.mm"
include "isfsupp.mm"
include "mpbir2and.mm"

theorem fdmfifsupp
  let wph: wff ph
  let cD: class D
  let cR: class R
  let cF: class F
  let cV: class V
  let cZ: class Z
  assume fdmfisuppfi.f: |- ( ph -> F : D --> R )
  assume fdmfisuppfi.d: |- ( ph -> D e. Fin )
  assume fdmfisuppfi.z: |- ( ph -> Z e. V )


  assert |- ( ph -> F finSupp Z )

  proof
    wph
    cF
    cZ
    cfsupp
    wbr
    #
    cF
    wfun
    #
    cF
    cZ
    csupp
    co
    cfn
    wcel
    #
    wph
    cD
    cR
    cF
    wf
    #
    @1
    fdmfisuppfi.f
    cD
    cR
    cF
    ffun
    syl
    wph
    cD
    cR
    cF
    cV
    cZ
    fdmfisuppfi.f
    fdmfisuppfi.d
    fdmfisuppfi.z
    fdmfisuppfi
    wph
    cF
    cvv
    wcel
    #
    cZ
    cV
    wcel
    @0
    @1
    @2
    wa
    wb
    wph
    cF
    cD
    wfn
    #
    cD
    cfn
    wcel
    @4
    wph
    @3
    @5
    fdmfisuppfi.f
    cD
    cR
    cF
    ffn
    syl
    fdmfisuppfi.d
    cD
    cfn
    cF
    fnex
    syl2anc
    fdmfisuppfi.z
    cF
    cvv
    cV
    cZ
    isfsupp
    syl2anc
    mpbir2and
end
