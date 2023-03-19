include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "uzssz.mm"
include "eqsstri.mm"

theorem uzssz2
  let cM: class M
  let cZ: class Z
  assume uzssz2.1: |- Z = ( ZZ>= ` M )


  assert |- Z C_ ZZ

  proof
    cZ
    cM
    cuz
    cfv
    cz
    uzssz2.1
    cM
    uzssz
    eqsstri
end
