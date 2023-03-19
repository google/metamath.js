include "ceupth.mm"
include "cfv.mm"
include "wbr.mm"
include "ctrls.mm"
include "cwlks.mm"
include "eupthistrl.mm"
include "trliswlk.mm"
include "syl.mm"

theorem eupthiswlk
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( EulerPaths ` G ) P -> F ( Walks ` G ) P )

  proof
    cF
    cP
    cG
    ceupth
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
    eupthistrl
    cP
    cF
    cG
    trliswlk
    syl
end
