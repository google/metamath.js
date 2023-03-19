include "ccycls.mm"
include "cfv.mm"
include "wbr.mm"
include "cpths.mm"
include "cwlks.mm"
include "cyclispth.mm"
include "pthiswlk.mm"
include "syl.mm"

theorem cycliswlk
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( Cycles ` G ) P -> F ( Walks ` G ) P )

  proof
    cF
    cP
    cG
    ccycls
    cfv
    wbr
    cF
    cP
    cG
    cpths
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
    cyclispth
    cP
    cF
    cG
    pthiswlk
    syl
end
