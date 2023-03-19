include "crn.mm"
include "wfn.mm"
include "wf.mm"
include "dffn3.mm"
include "sylib.mm"
include "fdmfisuppfi.mm"

theorem fndmfisuppfi
  let wph: wff ph
  let cD: class D
  let cF: class F
  let cV: class V
  let cZ: class Z
  assume fndmfisuppfi.f: |- ( ph -> F Fn D )
  assume fndmfisuppfi.d: |- ( ph -> D e. Fin )
  assume fndmfisuppfi.z: |- ( ph -> Z e. V )


  assert |- ( ph -> ( F supp Z ) e. Fin )

  proof
    wph
    cD
    cF
    crn
    #
    cF
    cV
    cZ
    wph
    cF
    cD
    wfn
    cD
    @0
    cF
    wf
    fndmfisuppfi.f
    cD
    cF
    dffn3
    sylib
    fndmfisuppfi.d
    fndmfisuppfi.z
    fdmfisuppfi
end
