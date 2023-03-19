include "cfzo.mm"
include "co.mm"
include "cfz.mm"
include "cuz.mm"
include "cfv.mm"
include "fzossfz.mm"
include "fzssuz.mm"
include "sstri.mm"

theorem fzossuz
  let cM: class M
  let cN: class N


  assert |- ( M ..^ N ) C_ ( ZZ>= ` M )

  proof
    cM
    cN
    cfzo
    co
    cM
    cN
    cfz
    co
    cM
    cuz
    cfv
    cM
    cN
    fzossfz
    cM
    cN
    fzssuz
    sstri
end
