include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wss.mm"
include "eluzfz1.mm"
include "adantr.mm"
include "simpr.mm"
include "eleqtrd.mm"
include "elfzuz.mm"
include "uzss.mm"
include "3syl.mm"
include "elfzuz2.mm"
include "eleqtrrd.mm"
include "eqssd.mm"
include "cz.mm"
include "wb.mm"
include "eluzel2.mm"
include "uz11.mm"
include "syl.mm"
include "mpbid.mm"
include "eluzfz2.mm"
include "elfzuz3.mm"
include "eluzelz.mm"
include "jca.mm"
include "ex.mm"
include "oveq12.mm"
include "impbid1.mm"

theorem fzopth
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` M ) -> ( ( M ... N ) = ( J ... K ) <-> ( M = J /\ N = K ) ) )

  proof
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    cM
    cN
    cfz
    co
    #
    cJ
    cK
    cfz
    co
    #
    wceq
    #
    cM
    cJ
    wceq
    #
    cN
    cK
    wceq
    #
    wa
    #
    @1
    @4
    @7
    @1
    @4
    wa
    #
    @5
    @6
    @8
    @0
    cJ
    cuz
    cfv
    #
    wceq
    #
    @5
    @8
    @0
    @9
    @8
    cM
    @3
    wcel
    #
    cM
    @9
    wcel
    @0
    @9
    wss
    @8
    cM
    @2
    @3
    @1
    cM
    @2
    wcel
    @4
    cM
    cN
    eluzfz1
    adantr
    @1
    @4
    simpr
    #
    eleqtrd
    #
    cM
    cJ
    cK
    elfzuz
    cJ
    cM
    uzss
    3syl
    @8
    cJ
    @2
    wcel
    cJ
    @0
    wcel
    @9
    @0
    wss
    @8
    cJ
    @3
    @2
    @8
    @11
    cK
    @9
    wcel
    #
    cJ
    @3
    wcel
    @13
    cM
    cJ
    cK
    elfzuz2
    #
    cJ
    cK
    eluzfz1
    3syl
    @12
    eleqtrrd
    cJ
    cM
    cN
    elfzuz
    cM
    cJ
    uzss
    3syl
    eqssd
    @8
    cM
    cz
    wcel
    #
    @10
    @5
    wb
    @1
    @16
    @4
    cM
    cN
    eluzel2
    adantr
    cM
    cJ
    uz11
    syl
    mpbid
    @8
    cN
    cuz
    cfv
    #
    cK
    cuz
    cfv
    #
    wceq
    #
    @6
    @8
    @17
    @18
    @8
    cK
    @2
    wcel
    cN
    @18
    wcel
    @17
    @18
    wss
    @8
    cK
    @3
    @2
    @8
    @11
    @14
    cK
    @3
    wcel
    @13
    @15
    cJ
    cK
    eluzfz2
    3syl
    @12
    eleqtrrd
    cK
    cM
    cN
    elfzuz3
    cK
    cN
    uzss
    3syl
    @8
    cN
    @3
    wcel
    cK
    @17
    wcel
    @18
    @17
    wss
    @8
    cN
    @2
    @3
    @1
    cN
    @2
    wcel
    @4
    cM
    cN
    eluzfz2
    adantr
    @12
    eleqtrd
    cN
    cJ
    cK
    elfzuz3
    cN
    cK
    uzss
    3syl
    eqssd
    @8
    cN
    cz
    wcel
    #
    @19
    @6
    wb
    @1
    @20
    @4
    cM
    cN
    eluzelz
    adantr
    cN
    cK
    uz11
    syl
    mpbid
    jca
    ex
    cM
    cJ
    cN
    cK
    cfz
    oveq12
    impbid1
end
