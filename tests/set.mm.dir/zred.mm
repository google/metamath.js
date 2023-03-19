include "cz.mm"
include "cr.mm"
include "zssre.mm"
include "sseldi.mm"

theorem zred
  let wph: wff ph
  let cA: class A
  assume zred.1: |- ( ph -> A e. ZZ )


  assert |- ( ph -> A e. RR )

  proof
    wph
    cz
    cr
    cA
    zssre
    zred.1
    sseldi
end
