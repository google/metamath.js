include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "caddc.mm"
include "cmin.mm"
include "cz.mm"
include "wb.mm"
include "elfzelz.mm"
include "fzrev3.mm"
include "syl.mm"
include "ibi.mm"

theorem fzrev3i
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ... N ) -> ( ( M + N ) - K ) e. ( M ... N ) )

  proof
    cK
    cM
    cN
    cfz
    co
    #
    wcel
    #
    cM
    cN
    caddc
    co
    cK
    cmin
    co
    @0
    wcel
    #
    @1
    cK
    cz
    wcel
    @1
    @2
    wb
    cK
    cM
    cN
    elfzelz
    cK
    cM
    cN
    fzrev3
    syl
    ibi
end
