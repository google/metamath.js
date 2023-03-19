include "cuz.mm"
include "cfv.mm"
include "cr.mm"
include "cz.mm"
include "uzssz.mm"
include "zssre.mm"
include "sstri.mm"
include "eqsstri.mm"

theorem uzssre2
  let cM: class M
  let cZ: class Z
  assume uzssre2.1: |- Z = ( ZZ>= ` M )


  assert |- Z C_ RR

  proof
    cZ
    cM
    cuz
    cfv
    #
    cr
    uzssre2.1
    @0
    cz
    cr
    cM
    uzssz
    zssre
    sstri
    eqsstri
end
