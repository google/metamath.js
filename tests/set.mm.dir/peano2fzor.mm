include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "wa.mm"
include "cmin.mm"
include "cfz.mm"
include "simpr.mm"
include "cz.mm"
include "wceq.mm"
include "elfzoel2.mm"
include "adantl.mm"
include "fzoval.mm"
include "syl.mm"
include "eleqtrd.mm"
include "peano2fzr.mm"
include "syldan.mm"
include "eleqtrrd.mm"

theorem peano2fzor
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( K e. ( ZZ>= ` M ) /\ ( K + 1 ) e. ( M ..^ N ) ) -> K e. ( M ..^ N ) )

  proof
    cK
    cM
    cuz
    cfv
    wcel
    #
    cK
    c1
    caddc
    co
    #
    cM
    cN
    cfzo
    co
    #
    wcel
    #
    wa
    #
    cK
    cM
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    @2
    @0
    @3
    @1
    @6
    wcel
    cK
    @6
    wcel
    @4
    @1
    @2
    @6
    @0
    @3
    simpr
    @4
    cN
    cz
    wcel
    #
    @2
    @6
    wceq
    @3
    @7
    @0
    @1
    cM
    cN
    elfzoel2
    adantl
    cM
    cN
    fzoval
    syl
    #
    eleqtrd
    cK
    cM
    @5
    peano2fzr
    syldan
    @8
    eleqtrrd
end
