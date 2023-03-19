include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "cr.mm"
include "uzssz.mm"
include "zssre.mm"
include "sstri.mm"

theorem uzssre
  let cM: class M


  assert |- ( ZZ>= ` M ) C_ RR

  proof
    cM
    cuz
    cfv
    cz
    cr
    cM
    uzssz
    zssre
    sstri
end
