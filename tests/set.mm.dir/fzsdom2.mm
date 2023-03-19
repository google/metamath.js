include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cfz.mm"
include "co.mm"
include "chash.mm"
include "csdm.mm"
include "cmin.mm"
include "c1.mm"
include "caddc.mm"
include "eluzelz.mm"
include "ad2antrr.mm"
include "zred.mm"
include "eluzel2.mm"
include "resubcld.mm"
include "simplr.mm"
include "1red.mm"
include "simpr.mm"
include "ltsub1dd.mm"
include "ltadd1dd.mm"
include "wceq.mm"
include "hashfz.mm"
include "cle.mm"
include "ltled.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "simpll.mm"
include "uztrn.mm"
include "syl2anc.mm"
include "syl.mm"
include "3brtr4d.mm"
include "cfn.mm"
include "wb.mm"
include "fzfi.mm"
include "hashsdom.mm"
include "mp2an.mm"
include "sylib.mm"

theorem fzsdom2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( B e. ( ZZ>= ` A ) /\ C e. ZZ ) /\ B < C ) -> ( A ... B ) ~< ( A ... C ) )

  proof
    cB
    cA
    cuz
    cfv
    #
    wcel
    #
    cC
    cz
    wcel
    #
    wa
    #
    cB
    cC
    clt
    wbr
    #
    wa
    #
    cA
    cB
    cfz
    co
    #
    chash
    cfv
    #
    cA
    cC
    cfz
    co
    #
    chash
    cfv
    #
    clt
    wbr
    #
    @6
    @8
    csdm
    wbr
    #
    @5
    cB
    cA
    cmin
    co
    #
    c1
    caddc
    co
    #
    cC
    cA
    cmin
    co
    #
    c1
    caddc
    co
    #
    @7
    @9
    clt
    @5
    @12
    @14
    c1
    @5
    cB
    cA
    @5
    cB
    @1
    cB
    cz
    wcel
    #
    @2
    @4
    cA
    cB
    eluzelz
    ad2antrr
    #
    zred
    #
    @5
    cA
    @1
    cA
    cz
    wcel
    @2
    @4
    cA
    cB
    eluzel2
    ad2antrr
    zred
    #
    resubcld
    @5
    cC
    cA
    @5
    cC
    @1
    @2
    @4
    simplr
    #
    zred
    #
    @19
    resubcld
    @5
    1red
    @5
    cB
    cC
    cA
    @18
    @21
    @19
    @3
    @4
    simpr
    #
    ltsub1dd
    ltadd1dd
    @1
    @7
    @13
    wceq
    @2
    @4
    cA
    cB
    hashfz
    ad2antrr
    @5
    cC
    @0
    wcel
    #
    @9
    @15
    wceq
    @5
    cC
    cB
    cuz
    cfv
    wcel
    #
    @1
    @23
    @5
    @16
    @2
    cB
    cC
    cle
    wbr
    @24
    @17
    @20
    @5
    cB
    cC
    @18
    @21
    @22
    ltled
    cB
    cC
    eluz2
    syl3anbrc
    @1
    @2
    @4
    simpll
    cB
    cC
    cA
    uztrn
    syl2anc
    cA
    cC
    hashfz
    syl
    3brtr4d
    @6
    cfn
    wcel
    @8
    cfn
    wcel
    @10
    @11
    wb
    cA
    cB
    fzfi
    cA
    cC
    fzfi
    @6
    @8
    hashsdom
    mp2an
    sylib
end
