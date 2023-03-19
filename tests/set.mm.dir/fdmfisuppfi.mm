include "csupp.mm"
include "co.mm"
include "ccnv.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "cfn.mm"
include "wcel.mm"
include "wceq.mm"
include "wf.mm"
include "fex.mm"
include "syl2anc.mm"
include "suppimacnv.mm"
include "fisuppfi.mm"
include "eqeltrd.mm"

theorem fdmfisuppfi
  let wph: wff ph
  let cD: class D
  let cR: class R
  let cF: class F
  let cV: class V
  let cZ: class Z
  assume fdmfisuppfi.f: |- ( ph -> F : D --> R )
  assume fdmfisuppfi.d: |- ( ph -> D e. Fin )
  assume fdmfisuppfi.z: |- ( ph -> Z e. V )


  assert |- ( ph -> ( F supp Z ) e. Fin )

  proof
    wph
    cF
    cZ
    csupp
    co
    #
    cF
    ccnv
    cvv
    cZ
    csn
    cdif
    #
    cima
    #
    cfn
    wph
    cF
    cvv
    wcel
    #
    cZ
    cV
    wcel
    @0
    @2
    wceq
    wph
    cD
    cR
    cF
    wf
    cD
    cfn
    wcel
    @3
    fdmfisuppfi.f
    fdmfisuppfi.d
    cD
    cR
    cfn
    cF
    fex
    syl2anc
    fdmfisuppfi.z
    cF
    cvv
    cV
    cZ
    suppimacnv
    syl2anc
    wph
    cD
    cR
    @1
    cF
    fdmfisuppfi.d
    fdmfisuppfi.f
    fisuppfi
    eqeltrd
end
