include "com.mm"
include "csdm.mm"
include "wbr.mm"
include "wa.mm"
include "cun.mm"
include "cfn.mm"
include "wcel.mm"
include "isfinite2.mm"
include "unfi.mm"
include "syl2an.mm"
include "cvv.mm"
include "wb.mm"
include "fin2inf.mm"
include "adantr.mm"
include "isfiniteg.mm"
include "syl.mm"
include "mpbid.mm"

theorem unfi2
  let cA: class A
  let cB: class B


  assert |- ( ( A ~< _om /\ B ~< _om ) -> ( A u. B ) ~< _om )

  proof
    cA
    com
    csdm
    wbr
    #
    cB
    com
    csdm
    wbr
    #
    wa
    #
    cA
    cB
    cun
    #
    cfn
    wcel
    #
    @3
    com
    csdm
    wbr
    #
    @0
    cA
    cfn
    wcel
    cB
    cfn
    wcel
    @4
    @1
    cA
    isfinite2
    cB
    isfinite2
    cA
    cB
    unfi
    syl2an
    @2
    com
    cvv
    wcel
    #
    @4
    @5
    wb
    @0
    @6
    @1
    cA
    fin2inf
    adantr
    @3
    isfiniteg
    syl
    mpbid
end
