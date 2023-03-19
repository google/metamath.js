include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "wo.mm"
include "fzosplitsn.mm"
include "eleq2d.mm"
include "elun.mm"
include "elsn2g.mm"
include "orbi2d.mm"
include "syl5bb.mm"
include "bitrd.mm"

theorem fzosplitsni
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( B e. ( ZZ>= ` A ) -> ( C e. ( A ..^ ( B + 1 ) ) <-> ( C e. ( A ..^ B ) \/ C = B ) ) )

  proof
    cB
    cA
    cuz
    cfv
    #
    wcel
    #
    cC
    cA
    cB
    c1
    caddc
    co
    cfzo
    co
    #
    wcel
    cC
    cA
    cB
    cfzo
    co
    #
    cB
    csn
    #
    cun
    #
    wcel
    #
    cC
    @3
    wcel
    #
    cC
    cB
    wceq
    #
    wo
    #
    @1
    @2
    @5
    cC
    cA
    cB
    fzosplitsn
    eleq2d
    @6
    @7
    cC
    @4
    wcel
    #
    wo
    @1
    @9
    cC
    @3
    @4
    elun
    @1
    @10
    @8
    @7
    cC
    cB
    @0
    elsn2g
    orbi2d
    syl5bb
    bitrd
end
