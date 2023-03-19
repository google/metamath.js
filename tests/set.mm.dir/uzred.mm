include "cz.mm"
include "cr.mm"
include "zssre.mm"
include "eluzelz2d.mm"
include "sseldi.mm"

theorem uzred
  let wph: wff ph
  let cA: class A
  let cM: class M
  let cZ: class Z
  assume uzred.1: |- Z = ( ZZ>= ` M )
  assume uzred.2: |- ( ph -> A e. Z )


  assert |- ( ph -> A e. RR )

  proof
    wph
    cz
    cr
    cA
    zssre
    wph
    cM
    cA
    cZ
    uzred.1
    uzred.2
    eluzelz2d
    sseldi
end
