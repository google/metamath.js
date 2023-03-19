include "cfsupp.mm"
include "wbr.mm"
include "csupp.mm"
include "co.mm"
include "cfn.mm"
include "wcel.mm"
include "cxp.mm"
include "id.mm"
include "fsuppimpd.mm"
include "xpfi.mm"
include "syl2an.mm"

theorem fsuppxpfi
  let cF: class F
  let cG: class G
  let cZ: class Z


  assert |- ( ( F finSupp Z /\ G finSupp Z ) -> ( ( F supp Z ) X. ( G supp Z ) ) e. Fin )

  proof
    cF
    cZ
    cfsupp
    wbr
    #
    cF
    cZ
    csupp
    co
    #
    cfn
    wcel
    cG
    cZ
    csupp
    co
    #
    cfn
    wcel
    @1
    @2
    cxp
    cfn
    wcel
    cG
    cZ
    cfsupp
    wbr
    #
    @0
    cF
    cZ
    @0
    id
    fsuppimpd
    @3
    cG
    cZ
    @3
    id
    fsuppimpd
    @1
    @2
    xpfi
    syl2an
end
