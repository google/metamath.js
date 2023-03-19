include "ccrcts.mm"
include "cfv.mm"
include "wbr.mm"
include "ctrls.mm"
include "cwlks.mm"
include "crctistrl.mm"
include "trliswlk.mm"
include "syl.mm"

theorem crctiswlk
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( Circuits ` G ) P -> F ( Walks ` G ) P )

  proof
    cF
    cP
    cG
    ccrcts
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
    crctistrl
    cP
    cF
    cG
    trliswlk
    syl
end
