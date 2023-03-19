include "cr.mm"
include "cxr.mm"
include "ressxr.mm"
include "uzred.mm"
include "sseldi.mm"

theorem uzxrd
  let wph: wff ph
  let cA: class A
  let cM: class M
  let cZ: class Z
  assume uzxrd.1: |- Z = ( ZZ>= ` M )
  assume uzxrd.2: |- ( ph -> A e. Z )


  assert |- ( ph -> A e. RR* )

  proof
    wph
    cr
    cxr
    cA
    ressxr
    wph
    cA
    cM
    cZ
    uzxrd.1
    uzxrd.2
    uzred
    sseldi
end
