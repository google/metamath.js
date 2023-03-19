include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "caddc.mm"
include "cconcat.mm"
include "ccatcl.mm"
include "adantr.mm"
include "elfz0fzfz0.mm"
include "adantl.mm"
include "cuz.mm"
include "wss.mm"
include "elfzuz2.mm"
include "fzss1.mm"
include "syl.mm"
include "sseld.mm"
include "impr.mm"
include "wb.mm"
include "ccatlen.mm"
include "wceq.mm"
include "eqcomi.mm"
include "a1i.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "mpbird.mm"
include "3jca.mm"

theorem swrdccatin12lem2c
  let cA: class A
  let cB: class B
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let vk: setvar k
  assume swrdccatin12.l: |- L = ( # ` A )


  assert |- ( ( ( A e. Word V /\ B e. Word V ) /\ ( M e. ( 0 ... L ) /\ N e. ( L ... ( L + ( # ` B ) ) ) ) ) -> ( ( A ++ B ) e. Word V /\ M e. ( 0 ... N ) /\ N e. ( 0 ... ( # ` ( A ++ B ) ) ) ) )

  proof
    cA
    cV
    cword
    #
    wcel
    cB
    @0
    wcel
    wa
    #
    cM
    cc0
    cL
    cfz
    co
    wcel
    #
    cN
    cL
    cL
    cB
    chash
    cfv
    #
    caddc
    co
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    cconcat
    co
    #
    @0
    wcel
    #
    cM
    cc0
    cN
    cfz
    co
    wcel
    #
    cN
    cc0
    @9
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    @1
    @10
    @7
    cV
    cA
    cB
    ccatcl
    adantr
    @7
    @11
    @1
    cL
    cM
    cN
    @4
    elfz0fzfz0
    adantl
    @8
    @14
    cN
    cc0
    @4
    cfz
    co
    #
    wcel
    #
    @1
    @2
    @6
    @16
    @1
    @2
    wa
    #
    @5
    @15
    cN
    @17
    cL
    cc0
    cuz
    cfv
    wcel
    #
    @5
    @15
    wss
    @2
    @18
    @1
    cM
    cc0
    cL
    elfzuz2
    adantl
    cL
    cc0
    @4
    fzss1
    syl
    sseld
    impr
    @1
    @14
    @16
    wb
    @7
    @1
    @13
    @15
    cN
    @1
    @12
    @4
    cc0
    cfz
    @1
    @12
    cA
    chash
    cfv
    #
    @3
    caddc
    co
    @4
    cV
    cA
    cB
    ccatlen
    @1
    @19
    cL
    @3
    caddc
    @19
    cL
    wceq
    @1
    cL
    @19
    swrdccatin12.l
    eqcomi
    a1i
    oveq1d
    eqtrd
    oveq2d
    eleq2d
    adantr
    mpbird
    3jca
end
