include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "cfzo.mm"
include "wceq.mm"
include "wo.mm"
include "elfzuz2.mm"
include "csn.mm"
include "cun.mm"
include "fzisfzounsn.mm"
include "eleq2d.mm"
include "elun.mm"
include "elsni.mm"
include "orim2i.mm"
include "sylbi.mm"
include "syl6bi.mm"
include "mpcom.mm"

theorem elfzr
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ... N ) -> ( K e. ( M ..^ N ) \/ K = N ) )

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
    cN
    cfzo
    co
    #
    wcel
    #
    cK
    cN
    wceq
    #
    wo
    #
    cK
    cM
    cN
    elfzuz2
    @0
    @2
    cK
    @3
    cN
    csn
    #
    cun
    #
    wcel
    #
    @6
    @0
    @1
    @8
    cK
    cM
    cN
    fzisfzounsn
    eleq2d
    @9
    @4
    cK
    @7
    wcel
    #
    wo
    @6
    cK
    @3
    @7
    elun
    @10
    @5
    @4
    cK
    cN
    elsni
    orim2i
    sylbi
    syl6bi
    mpcom
end
