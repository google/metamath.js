include "cpths.mm"
include "cfv.mm"
include "wbr.mm"
include "ctrls.mm"
include "cwlks.mm"
include "pthistrl.mm"
include "trliswlk.mm"
include "syl.mm"

theorem pthiswlk
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( Paths ` G ) P -> F ( Walks ` G ) P )

  proof
    cF
    cP
    cG
    cpths
    cfv
    wbr
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    cP
    cF
    cG
    pthistrl
    cP
    cF
    cG
    trliswlk
    syl
end
