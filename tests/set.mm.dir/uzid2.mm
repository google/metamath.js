include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "eluzelz.mm"
include "uzid.mm"
include "syl.mm"

theorem uzid2
  let cM: class M
  let cN: class N


  assert |- ( M e. ( ZZ>= ` N ) -> M e. ( ZZ>= ` M ) )

  proof
    cM
    cN
    cuz
    cfv
    wcel
    cM
    cz
    wcel
    cM
    cM
    cuz
    cfv
    wcel
    cN
    cM
    eluzelz
    cM
    uzid
    syl
end
