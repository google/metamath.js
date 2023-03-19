include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cz.mm"
include "c1.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "id.mm"
include "elfzoel2.mm"
include "wa.mm"
include "cfz.mm"
include "simpl.mm"
include "wceq.mm"
include "fzoval.mm"
include "adantl.mm"
include "eleqtrd.mm"
include "elfzle2.mm"
include "syl.mm"
include "syl2anc.mm"

theorem elfzolem1
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ..^ N ) -> K <_ ( N - 1 ) )

  proof
    cK
    cM
    cN
    cfzo
    co
    #
    wcel
    #
    @1
    cN
    cz
    wcel
    #
    cK
    cN
    c1
    cmin
    co
    #
    cle
    wbr
    #
    @1
    id
    cK
    cM
    cN
    elfzoel2
    @1
    @2
    wa
    #
    cK
    cM
    @3
    cfz
    co
    #
    wcel
    @4
    @5
    cK
    @0
    @6
    @1
    @2
    simpl
    @2
    @0
    @6
    wceq
    @1
    cM
    cN
    fzoval
    adantl
    eleqtrd
    cK
    cM
    @3
    elfzle2
    syl
    syl2anc
end
