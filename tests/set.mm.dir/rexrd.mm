include "cr.mm"
include "cxr.mm"
include "ressxr.mm"
include "sseldi.mm"

theorem rexrd
  let wph: wff ph
  let cA: class A
  assume rexrd.1: |- ( ph -> A e. RR )


  assert |- ( ph -> A e. RR* )

  proof
    wph
    cr
    cxr
    cA
    ressxr
    rexrd.1
    sseldi
end
