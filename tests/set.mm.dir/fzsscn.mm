include "cfz.mm"
include "co.mm"
include "cz.mm"
include "cc.mm"
include "fzssz.mm"
include "zsscn.mm"
include "sstri.mm"

theorem fzsscn
  let cM: class M
  let cN: class N


  assert |- ( M ... N ) C_ CC

  proof
    cM
    cN
    cfz
    co
    cz
    cc
    cM
    cN
    fzssz
    zsscn
    sstri
end
