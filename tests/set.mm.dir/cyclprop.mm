include "ccycls.mm"
include "cfv.mm"
include "wbr.mm"
include "cpths.mm"
include "cc0.mm"
include "chash.mm"
include "wceq.mm"
include "wa.mm"
include "iscycl.mm"
include "biimpi.mm"

theorem cyclprop
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( Cycles ` G ) P -> ( F ( Paths ` G ) P /\ ( P ` 0 ) = ( P ` ( # ` F ) ) ) )

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
    iscycl
    biimpi
end
