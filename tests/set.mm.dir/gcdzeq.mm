include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cgcd.mm"
include "co.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "nnz.mm"
include "gcddvds.mm"
include "sylan.mm"
include "simprd.mm"
include "breq1.mm"
include "syl5ibcom.mm"
include "cle.mm"
include "adantr.mm"
include "iddvds.mm"
include "syl.mm"
include "cc0.mm"
include "wn.mm"
include "wi.mm"
include "simpr.mm"
include "wne.mm"
include "nnne0.mm"
include "simpl.mm"
include "necon3ai.mm"
include "dvdslegcd.mm"
include "syl31anc.mm"
include "mpand.mm"
include "simpld.mm"
include "cn0.mm"
include "gcdcl.mm"
include "nn0zd.mm"
include "dvdsle.mm"
include "syl2anc.mm"
include "mpd.mm"
include "jctild.mm"
include "nn0red.mm"
include "cr.mm"
include "nnre.mm"
include "letri3d.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem gcdzeq
  let cA: class A
  let cB: class B


  assert |- ( ( A e. NN /\ B e. ZZ ) -> ( ( A gcd B ) = A <-> A || B ) )

  proof
    cA
    cn
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    cA
    cB
    cgcd
    co
    #
    cA
    wceq
    #
    cA
    cB
    cdvds
    wbr
    #
    @2
    @3
    cB
    cdvds
    wbr
    #
    @4
    @5
    @2
    @3
    cA
    cdvds
    wbr
    #
    @6
    @0
    cA
    cz
    wcel
    #
    @1
    @7
    @6
    wa
    cA
    nnz
    #
    cA
    cB
    gcddvds
    sylan
    #
    simprd
    @3
    cA
    cB
    cdvds
    breq1
    syl5ibcom
    @2
    @5
    @3
    cA
    cle
    wbr
    #
    cA
    @3
    cle
    wbr
    #
    wa
    @4
    @2
    @5
    @12
    @11
    @2
    cA
    cA
    cdvds
    wbr
    #
    @5
    @12
    @2
    @8
    @13
    @0
    @8
    @1
    @9
    adantr
    #
    cA
    iddvds
    syl
    @2
    @8
    @8
    @1
    cA
    cc0
    wceq
    #
    cB
    cc0
    wceq
    #
    wa
    #
    wn
    #
    @13
    @5
    wa
    @12
    wi
    @14
    @14
    @0
    @1
    simpr
    @0
    @18
    @1
    @0
    cA
    cc0
    wne
    @18
    cA
    nnne0
    @17
    cA
    cc0
    @15
    @16
    simpl
    necon3ai
    syl
    adantr
    cA
    cA
    cB
    dvdslegcd
    syl31anc
    mpand
    @2
    @7
    @11
    @2
    @7
    @6
    @10
    simpld
    @2
    @3
    cz
    wcel
    @0
    @7
    @11
    wi
    @2
    @3
    @0
    @8
    @1
    @3
    cn0
    wcel
    @9
    cA
    cB
    gcdcl
    sylan
    #
    nn0zd
    @0
    @1
    simpl
    @3
    cA
    dvdsle
    syl2anc
    mpd
    jctild
    @2
    @3
    cA
    @2
    @3
    @19
    nn0red
    @0
    cA
    cr
    wcel
    @1
    cA
    nnre
    adantr
    letri3d
    sylibrd
    impbid
end
