include "wfn.mm"
include "cdm.mm"
include "wceq.mm"
include "fndm.mm"
include "syl.mm"

theorem fndmd
  let wph: wff ph
  let cA: class A
  let cF: class F
  assume fndmd.1: |- ( ph -> F Fn A )


  assert |- ( ph -> dom F = A )

  proof
    wph
    cF
    cA
    wfn
    cF
    cdm
    cA
    wceq
    fndmd.1
    cA
    cF
    fndm
    syl
end
