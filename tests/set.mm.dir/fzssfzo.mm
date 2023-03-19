include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cfz.mm"
include "c1.mm"
include "cmin.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "cz.mm"
include "wceq.mm"
include "elfzoel2.mm"
include "fzoval.mm"
include "syl.mm"
include "eleq2d.mm"
include "ibi.mm"
include "elfzuz3.mm"
include "fzss2.mm"
include "3syl.mm"
include "sseqtr4d.mm"

theorem fzssfzo
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ..^ N ) -> ( M ... K ) C_ ( M ..^ N ) )

  proof
    cK
    cM
    cN
    cfzo
    co
    #
    wcel
    #
    cM
    cK
    cfz
    co
    #
    cM
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    @0
    @1
    cK
    @4
    wcel
    #
    @3
    cK
    cuz
    cfv
    wcel
    @2
    @4
    wss
    @1
    @5
    @1
    @0
    @4
    cK
    @1
    cN
    cz
    wcel
    @0
    @4
    wceq
    cK
    cM
    cN
    elfzoel2
    cM
    cN
    fzoval
    syl
    #
    eleq2d
    ibi
    cK
    cM
    @3
    elfzuz3
    cK
    cM
    @3
    fzss2
    3syl
    @6
    sseqtr4d
end
