include "ccrcts.mm"
include "cfv.mm"
include "wbr.mm"
include "ctrls.mm"
include "cc0.mm"
include "chash.mm"
include "wceq.mm"
include "wa.mm"
include "iscrct.mm"
include "biimpi.mm"

theorem crctprop
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( Circuits ` G ) P -> ( F ( Trails ` G ) P /\ ( P ` 0 ) = ( P ` ( # ` F ) ) ) )

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
    cc0
    cP
    cfv
    cF
    chash
    cfv
    cP
    cfv
    wceq
    wa
    cP
    cF
    cG
    iscrct
    biimpi
end
