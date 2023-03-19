include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wfun.mm"
include "csupp.mm"
include "co.mm"
include "cfn.mm"
include "relfsupp.mm"
include "brrelexi.mm"
include "brrelex2i.mm"
include "jca.mm"
include "isfsupp.mm"
include "biimpd.mm"
include "mpcom.mm"

theorem fsuppimp
  let cR: class R
  let cZ: class Z


  assert |- ( R finSupp Z -> ( Fun R /\ ( R supp Z ) e. Fin ) )

  proof
    cR
    cvv
    wcel
    #
    cZ
    cvv
    wcel
    #
    wa
    #
    cR
    cZ
    cfsupp
    wbr
    #
    cR
    wfun
    cR
    cZ
    csupp
    co
    cfn
    wcel
    wa
    #
    @3
    @0
    @1
    cR
    cZ
    cfsupp
    relfsupp
    brrelexi
    cR
    cZ
    cfsupp
    relfsupp
    brrelex2i
    jca
    @2
    @3
    @4
    cR
    cvv
    cvv
    cZ
    isfsupp
    biimpd
    mpcom
end
