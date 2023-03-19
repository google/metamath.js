include "wcel.mm"
include "wfun.mm"
include "wa.mm"
include "cfsupp.mm"
include "wbr.mm"
include "csupp.mm"
include "co.mm"
include "wss.mm"
include "cvv.mm"
include "cfn.mm"
include "simpll.mm"
include "simplr.mm"
include "relfsupp.mm"
include "brrelex2i.mm"
include "ad2antrl.mm"
include "id.mm"
include "fsuppimpd.mm"
include "anim1i.mm"
include "adantl.mm"
include "suppssfifsupp.mm"
include "syl31anc.mm"

theorem fsuppsssupp
  let cF: class F
  let cG: class G
  let cV: class V
  let cZ: class Z


  assert |- ( ( ( G e. V /\ Fun G ) /\ ( F finSupp Z /\ ( G supp Z ) C_ ( F supp Z ) ) ) -> G finSupp Z )

  proof
    cG
    cV
    wcel
    #
    cG
    wfun
    #
    wa
    #
    cF
    cZ
    cfsupp
    wbr
    #
    cG
    cZ
    csupp
    co
    cF
    cZ
    csupp
    co
    #
    wss
    #
    wa
    #
    wa
    @0
    @1
    cZ
    cvv
    wcel
    #
    @4
    cfn
    wcel
    #
    @5
    wa
    #
    cG
    cZ
    cfsupp
    wbr
    @0
    @1
    @6
    simpll
    @0
    @1
    @6
    simplr
    @3
    @7
    @2
    @5
    cF
    cZ
    cfsupp
    relfsupp
    brrelex2i
    ad2antrl
    @6
    @9
    @2
    @3
    @8
    @5
    @3
    cF
    cZ
    @3
    id
    fsuppimpd
    anim1i
    adantl
    @4
    cG
    cV
    cvv
    cZ
    suppssfifsupp
    syl31anc
end
