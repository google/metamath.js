include "wcel.mm"
include "wfun.mm"
include "w3a.mm"
include "cfn.mm"
include "csupp.mm"
include "co.mm"
include "wss.mm"
include "wa.mm"
include "cfsupp.mm"
include "wbr.mm"
include "ssfi.mm"
include "adantl.mm"
include "wb.mm"
include "3ancoma.mm"
include "biimpi.mm"
include "adantr.mm"
include "funisfsupp.mm"
include "syl.mm"
include "mpbird.mm"

theorem suppssfifsupp
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let cZ: class Z


  assert |- ( ( ( G e. V /\ Fun G /\ Z e. W ) /\ ( F e. Fin /\ ( G supp Z ) C_ F ) ) -> G finSupp Z )

  proof
    cG
    cV
    wcel
    #
    cG
    wfun
    #
    cZ
    cW
    wcel
    #
    w3a
    #
    cF
    cfn
    wcel
    cG
    cZ
    csupp
    co
    #
    cF
    wss
    wa
    #
    wa
    #
    cG
    cZ
    cfsupp
    wbr
    #
    @4
    cfn
    wcel
    #
    @5
    @8
    @3
    cF
    @4
    ssfi
    adantl
    @6
    @1
    @0
    @2
    w3a
    #
    @7
    @8
    wb
    @3
    @9
    @5
    @3
    @9
    @0
    @1
    @2
    3ancoma
    biimpi
    adantr
    cG
    cV
    cW
    cZ
    funisfsupp
    syl
    mpbird
end
