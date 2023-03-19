include "cfz.mm"
include "co.mm"
include "cz.mm"
include "cr.mm"
include "fzssz.mm"
include "zssre.mm"
include "sstri.mm"

theorem fzssre
  let cM: class M
  let cN: class N


  assert |- ( M ... N ) C_ RR

  proof
    cM
    cN
    cfz
    co
    cz
    cr
    cM
    cN
    fzssz
    zssre
    sstri
end
