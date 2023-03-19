include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cfzo.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cfz.mm"
include "fzofzp1.mm"
include "wa.mm"
include "cmin.mm"
include "simpl.mm"
include "cz.mm"
include "eluzelz.mm"
include "elfzuz3.mm"
include "eluzp1m1.mm"
include "syl2an.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "wceq.mm"
include "elfzel2.mm"
include "adantl.mm"
include "fzoval.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "ex.mm"
include "impbid2.mm"

theorem fzofzp1b
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( C e. ( ZZ>= ` A ) -> ( C e. ( A ..^ B ) <-> ( C + 1 ) e. ( A ... B ) ) )

  proof
    cC
    cA
    cuz
    cfv
    wcel
    #
    cC
    cA
    cB
    cfzo
    co
    #
    wcel
    #
    cC
    c1
    caddc
    co
    #
    cA
    cB
    cfz
    co
    wcel
    #
    cA
    cB
    cC
    fzofzp1
    @0
    @4
    @2
    @0
    @4
    wa
    #
    cC
    cA
    cB
    c1
    cmin
    co
    #
    cfz
    co
    #
    @1
    @5
    @0
    @6
    cC
    cuz
    cfv
    wcel
    #
    cC
    @7
    wcel
    @0
    @4
    simpl
    @0
    cC
    cz
    wcel
    cB
    @3
    cuz
    cfv
    wcel
    @8
    @4
    cA
    cC
    eluzelz
    @3
    cA
    cB
    elfzuz3
    cC
    cB
    eluzp1m1
    syl2an
    cC
    cA
    @6
    elfzuzb
    sylanbrc
    @5
    cB
    cz
    wcel
    #
    @1
    @7
    wceq
    @4
    @9
    @0
    @3
    cA
    cB
    elfzel2
    adantl
    cA
    cB
    fzoval
    syl
    eleqtrrd
    ex
    impbid2
end
