include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "cfzo.mm"
include "w3o.mm"
include "elfzuz2.mm"
include "csn.mm"
include "cun.mm"
include "fzpred.mm"
include "eleq2d.mm"
include "wo.mm"
include "elsni.mm"
include "elfzr.mm"
include "orim12i.mm"
include "elun.mm"
include "3orass.mm"
include "3imtr4i.mm"
include "syl6bi.mm"
include "mpcom.mm"

theorem elfzlmr
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ... N ) -> ( K = M \/ K e. ( ( M + 1 ) ..^ N ) \/ K = N ) )

  proof
    cN
    cM
    cuz
    cfv
    wcel
    #
    cK
    cM
    cN
    cfz
    co
    #
    wcel
    #
    cK
    cM
    wceq
    #
    cK
    cM
    c1
    caddc
    co
    #
    cN
    cfzo
    co
    wcel
    #
    cK
    cN
    wceq
    #
    w3o
    #
    cK
    cM
    cN
    elfzuz2
    @0
    @2
    cK
    cM
    csn
    #
    @4
    cN
    cfz
    co
    #
    cun
    #
    wcel
    #
    @7
    @0
    @1
    @10
    cK
    cM
    cN
    fzpred
    eleq2d
    cK
    @8
    wcel
    #
    cK
    @9
    wcel
    #
    wo
    @3
    @5
    @6
    wo
    #
    wo
    @11
    @7
    @12
    @3
    @13
    @14
    cK
    cM
    elsni
    cK
    @4
    cN
    elfzr
    orim12i
    cK
    @8
    @9
    elun
    @3
    @5
    @6
    3orass
    3imtr4i
    syl6bi
    mpcom
end
