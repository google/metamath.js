include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cdvds.mm"
include "wbr.mm"
include "wceq.mm"
include "wne.mm"
include "wn.mm"
include "wa.mm"
include "cle.mm"
include "clt.mm"
include "elfzolt2.mm"
include "elfzoelz.mm"
include "zred.mm"
include "elfzoel2.mm"
include "ltnled.mm"
include "mpbid.mm"
include "adantr.mm"
include "cz.mm"
include "cn.mm"
include "wi.mm"
include "cn0.mm"
include "csn.mm"
include "cdif.mm"
include "elfzonn0.mm"
include "simpr.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "dfn2.mm"
include "syl6eleqr.mm"
include "dvdsle.mm"
include "syl2anc.mm"
include "mtod.mm"
include "ex.mm"
include "necon4ad.mm"
include "dvds0.mm"
include "syl.mm"
include "breq2.mm"
include "syl5ibrcom.mm"
include "impbid.mm"

theorem fzo0dvdseq
  let cA: class A
  let cB: class B


  assert |- ( B e. ( 0 ..^ A ) -> ( A || B <-> B = 0 ) )

  proof
    cB
    cc0
    cA
    cfzo
    co
    wcel
    #
    cA
    cB
    cdvds
    wbr
    #
    cB
    cc0
    wceq
    #
    @0
    @1
    cB
    cc0
    @0
    cB
    cc0
    wne
    #
    @1
    wn
    @0
    @3
    wa
    #
    @1
    cA
    cB
    cle
    wbr
    #
    @0
    @5
    wn
    #
    @3
    @0
    cB
    cA
    clt
    wbr
    @6
    cB
    cc0
    cA
    elfzolt2
    @0
    cB
    cA
    @0
    cB
    cB
    cc0
    cA
    elfzoelz
    zred
    @0
    cA
    cB
    cc0
    cA
    elfzoel2
    #
    zred
    ltnled
    mpbid
    adantr
    @4
    cA
    cz
    wcel
    #
    cB
    cn
    wcel
    @1
    @5
    wi
    @0
    @8
    @3
    @7
    adantr
    @4
    cB
    cn0
    cc0
    csn
    cdif
    #
    cn
    @4
    cB
    cn0
    wcel
    #
    @3
    cB
    @9
    wcel
    @0
    @10
    @3
    cB
    cA
    elfzonn0
    adantr
    @0
    @3
    simpr
    cB
    cn0
    cc0
    eldifsn
    sylanbrc
    dfn2
    syl6eleqr
    cA
    cB
    dvdsle
    syl2anc
    mtod
    ex
    necon4ad
    @0
    @1
    @2
    cA
    cc0
    cdvds
    wbr
    #
    @0
    @8
    @11
    @7
    cA
    dvds0
    syl
    cB
    cc0
    cA
    cdvds
    breq2
    syl5ibrcom
    impbid
end
