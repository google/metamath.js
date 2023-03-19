include "cclwwlkn.mm"
include "co.mm"
include "wcel.mm"
include "cclwwlk.mm"
include "cfv.mm"
include "chash.mm"
include "wceq.mm"
include "isclwwlkn.mm"
include "simplbi.mm"

theorem clwwlkclwwlkn
  let cG: class G
  let cN: class N
  let cW: class W


  assert |- ( W e. ( N ClWWalksN G ) -> W e. ( ClWWalks ` G ) )

  proof
    cW
    cN
    cG
    cclwwlkn
    co
    wcel
    cW
    cG
    cclwwlk
    cfv
    wcel
    cW
    chash
    cfv
    cN
    wceq
    cG
    cN
    cW
    isclwwlkn
    simplbi
end
