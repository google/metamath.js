include "ccrcts.mm"
include "cfv.mm"
include "wbr.mm"
include "ctrls.mm"
include "cc0.mm"
include "chash.mm"
include "wceq.mm"
include "wa.mm"
include "cclwlks.mm"
include "crctprop.mm"
include "cwlks.mm"
include "trliswlk.mm"
include "isclwlk.mm"
include "biimpri.mm"
include "sylan.mm"
include "syl.mm"

theorem crctisclwlk
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( Circuits ` G ) P -> F ( ClWalks ` G ) P )

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
    #
    cc0
    cP
    cfv
    cF
    chash
    cfv
    cP
    cfv
    wceq
    #
    wa
    cF
    cP
    cG
    cclwlks
    cfv
    wbr
    #
    cP
    cF
    cG
    crctprop
    @0
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    @1
    @2
    cP
    cF
    cG
    trliswlk
    @2
    @3
    @1
    wa
    cP
    cF
    cG
    isclwlk
    biimpri
    sylan
    syl
end
