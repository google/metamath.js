include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cmin.mm"
include "cc0.mm"
include "cfzo.mm"
include "cz.mm"
include "wb.mm"
include "1zzd.mm"
include "elfzel2.mm"
include "elfzelz.mm"
include "fzsubel.mm"
include "syl22anc.mm"
include "ibi.mm"
include "1m1e0.mm"
include "oveq1i.mm"
include "syl6eleq.mm"
include "wceq.mm"
include "fzoval.mm"
include "syl.mm"
include "eleqtrrd.mm"

theorem fz1fzo0m1
  let cM: class M
  let cN: class N


  assert |- ( M e. ( 1 ... N ) -> ( M - 1 ) e. ( 0 ..^ N ) )

  proof
    cM
    c1
    cN
    cfz
    co
    wcel
    #
    cM
    c1
    cmin
    co
    #
    cc0
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    cc0
    cN
    cfzo
    co
    #
    @0
    @1
    c1
    c1
    cmin
    co
    #
    @2
    cfz
    co
    #
    @3
    @0
    @1
    @6
    wcel
    #
    @0
    c1
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cM
    cz
    wcel
    @8
    @0
    @7
    wb
    @0
    1zzd
    #
    cM
    c1
    cN
    elfzel2
    #
    cM
    c1
    cN
    elfzelz
    @10
    cM
    c1
    c1
    cN
    fzsubel
    syl22anc
    ibi
    @5
    cc0
    @2
    cfz
    1m1e0
    oveq1i
    syl6eleq
    @0
    @9
    @4
    @3
    wceq
    @11
    cc0
    cN
    fzoval
    syl
    eleqtrrd
end
