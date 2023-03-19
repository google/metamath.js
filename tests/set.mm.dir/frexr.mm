include "cr.mm"
include "cxr.mm"
include "wss.mm"
include "ressxr.mm"
include "a1i.mm"
include "fssd.mm"

theorem frexr
  let wph: wff ph
  let cA: class A
  let cF: class F
  assume frexr.1: |- ( ph -> F : A --> RR )


  assert |- ( ph -> F : A --> RR* )

  proof
    wph
    cA
    cr
    cxr
    cF
    frexr.1
    cr
    cxr
    wss
    wph
    ressxr
    a1i
    fssd
end
