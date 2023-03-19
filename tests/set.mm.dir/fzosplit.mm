include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cfzo.mm"
include "cun.mm"
include "cv.mm"
include "wa.mm"
include "wo.mm"
include "cz.mm"
include "simpr.mm"
include "elfzelz.mm"
include "adantr.mm"
include "fzospliti.mm"
include "syl2anc.mm"
include "elun.mm"
include "sylibr.mm"
include "ex.mm"
include "ssrdv.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "elfzuz3.mm"
include "fzoss2.mm"
include "syl.mm"
include "elfzuz.mm"
include "fzoss1.mm"
include "unssd.mm"
include "eqssd.mm"

theorem fzosplit
  let cB: class B
  let cC: class C
  let cD: class D
  let cA: class A
  let vx: setvar x


  assert |- ( D e. ( B ... C ) -> ( B ..^ C ) = ( ( B ..^ D ) u. ( D ..^ C ) ) )

  proof
    cD
    cB
    cC
    cfz
    co
    wcel
    #
    cB
    cC
    cfzo
    co
    #
    cB
    cD
    cfzo
    co
    #
    cD
    cC
    cfzo
    co
    #
    cun
    #
    @0
    vx
    @1
    @4
    @0
    vx
    cv
    #
    @1
    wcel
    #
    @5
    @4
    wcel
    #
    @0
    @6
    wa
    #
    @5
    @2
    wcel
    @5
    @3
    wcel
    wo
    #
    @7
    @8
    @6
    cD
    cz
    wcel
    #
    @9
    @0
    @6
    simpr
    @0
    @10
    @6
    cD
    cB
    cC
    elfzelz
    adantr
    @5
    cB
    cC
    cD
    fzospliti
    syl2anc
    @5
    @2
    @3
    elun
    sylibr
    ex
    ssrdv
    @0
    @2
    @3
    @1
    @0
    cC
    cD
    cuz
    cfv
    wcel
    @2
    @1
    wss
    cD
    cB
    cC
    elfzuz3
    cD
    cB
    cC
    fzoss2
    syl
    @0
    cD
    cB
    cuz
    cfv
    wcel
    @3
    @1
    wss
    cD
    cB
    cC
    elfzuz
    cD
    cB
    cC
    fzoss1
    syl
    unssd
    eqssd
end
