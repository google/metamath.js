include "cusgr.mm"
include "wcel.mm"
include "cuspgr.mm"
include "ccrcts.mm"
include "cfv.mm"
include "wbr.mm"
include "chash.mm"
include "c2.mm"
include "wne.mm"
include "ccycls.mm"
include "usgruspgr.mm"
include "cycliscrct.mm"
include "uspgrn2crct.mm"
include "syl2an.mm"

theorem usgrn2cycl
  let cP: class P
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vk: setvar k


  assert |- ( ( G e. USGraph /\ F ( Cycles ` G ) P ) -> ( # ` F ) =/= 2 )

  proof
    cG
    cusgr
    wcel
    cG
    cuspgr
    wcel
    cF
    cP
    cG
    ccrcts
    cfv
    wbr
    cF
    chash
    cfv
    c2
    wne
    cF
    cP
    cG
    ccycls
    cfv
    wbr
    cG
    usgruspgr
    cP
    cF
    cG
    cycliscrct
    cP
    cF
    cG
    uspgrn2crct
    syl2an
end
