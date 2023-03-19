include "cclwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cwlks.mm"
include "cc0.mm"
include "chash.mm"
include "wceq.mm"
include "isclwlk.mm"
include "simplbi.mm"

theorem clwlkiswlk
  let cP: class P
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vp: setvar p


  assert |- ( F ( ClWalks ` G ) P -> F ( Walks ` G ) P )

  proof
    cF
    cP
    cG
    cclwlks
    cfv
    wbr
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    cc0
    cP
    cfv
    cF
    chash
    cfv
    cP
    cfv
    wceq
    cP
    cF
    cG
    isclwlk
    simplbi
end
