include "cspths.mm"
include "cfv.mm"
include "wbr.mm"
include "cpths.mm"
include "cwlks.mm"
include "spthispth.mm"
include "pthiswlk.mm"
include "syl.mm"

theorem spthiswlk
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( SPaths ` G ) P -> F ( Walks ` G ) P )

  proof
    cF
    cP
    cG
    cspths
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
    spthispth
    cP
    cF
    cG
    pthiswlk
    syl
end
