include "cfzo.mm"
include "co.mm"
include "cfz.mm"
include "cz.mm"
include "fzossfz.mm"
include "fzssz.mm"
include "sstri.mm"

theorem fzossz
  let cM: class M
  let cN: class N


  assert |- ( M ..^ N ) C_ ZZ

  proof
    cM
    cN
    cfzo
    co
    cM
    cN
    cfz
    co
    cz
    cM
    cN
    fzossfz
    cM
    cN
    fzssz
    sstri
end
