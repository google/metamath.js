include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "cfn.mm"
include "df-pr.mm"
include "wcel.mm"
include "snfi.mm"
include "unfi.mm"
include "mp2an.mm"
include "eqeltri.mm"

theorem prfi
  let cA: class A
  let cB: class B


  assert |- { A , B } e. Fin

  proof
    cA
    cB
    cpr
    cA
    csn
    #
    cB
    csn
    #
    cun
    #
    cfn
    cA
    cB
    df-pr
    @0
    cfn
    wcel
    @1
    cfn
    wcel
    @2
    cfn
    wcel
    cA
    snfi
    cB
    snfi
    @0
    @1
    unfi
    mp2an
    eqeltri
end
