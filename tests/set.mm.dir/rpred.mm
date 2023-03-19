include "crp.mm"
include "cr.mm"
include "rpssre.mm"
include "sseldi.mm"

theorem rpred
  let wph: wff ph
  let cA: class A
  assume rpred.1: |- ( ph -> A e. RR+ )


  assert |- ( ph -> A e. RR )

  proof
    wph
    crp
    cr
    cA
    rpssre
    rpred.1
    sseldi
end
