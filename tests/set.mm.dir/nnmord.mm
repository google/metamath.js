include "com.mm"
include "wcel.mm"
include "w3a.mm"
include "c0.mm"
include "wa.mm"
include "comu.mm"
include "co.mm"
include "wi.mm"
include "nnmordi.mm"
include "ex.mm"
include "com23.mm"
include "impd.mm"
include "3adant1.mm"
include "wne.mm"
include "ne0i.mm"
include "wceq.mm"
include "nnm0r.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "necon3d.mm"
include "syl5.mm"
include "adantr.mm"
include "wb.mm"
include "word.mm"
include "nnord.mm"
include "ord0eln0.mm"
include "syl.mm"
include "adantl.mm"
include "sylibrd.mm"
include "wo.mm"
include "wn.mm"
include "oveq2.mm"
include "a1i.mm"
include "3adantl2.mm"
include "orim12d.mm"
include "con3d.mm"
include "simpl3.mm"
include "simpl1.mm"
include "nnmcl.mm"
include "syl2anc.mm"
include "simpl2.mm"
include "ordtri2.mm"
include "syl2an.mm"
include "3imtr4d.mm"
include "mpdd.mm"
include "jcad.mm"
include "impbid.mm"

theorem nnmord
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. _om /\ B e. _om /\ C e. _om ) -> ( ( A e. B /\ (/) e. C ) <-> ( C .o A ) e. ( C .o B ) ) )

  proof
    cA
    com
    wcel
    #
    cB
    com
    wcel
    #
    cC
    com
    wcel
    #
    w3a
    #
    cA
    cB
    wcel
    #
    c0
    cC
    wcel
    #
    wa
    #
    cC
    cA
    comu
    co
    #
    cC
    cB
    comu
    co
    #
    wcel
    #
    @1
    @2
    @6
    @9
    wi
    @0
    @1
    @2
    wa
    #
    @4
    @5
    @9
    @10
    @5
    @4
    @9
    @10
    @5
    @4
    @9
    wi
    cA
    cB
    cC
    nnmordi
    ex
    com23
    impd
    3adant1
    @3
    @9
    @4
    @5
    @3
    @9
    @5
    @4
    @1
    @2
    @9
    @5
    wi
    @0
    @10
    @9
    cC
    c0
    wne
    #
    @5
    @1
    @9
    @11
    wi
    @2
    @9
    @8
    c0
    wne
    @1
    @11
    @8
    @7
    ne0i
    @1
    cC
    c0
    @8
    c0
    @1
    @8
    c0
    wceq
    cC
    c0
    wceq
    #
    c0
    cB
    comu
    co
    #
    c0
    wceq
    cB
    nnm0r
    @12
    @8
    @13
    c0
    cC
    c0
    cB
    comu
    oveq1
    eqeq1d
    syl5ibrcom
    necon3d
    syl5
    adantr
    @2
    @5
    @11
    wb
    #
    @1
    @2
    cC
    word
    @14
    cC
    nnord
    cC
    ord0eln0
    syl
    adantl
    sylibrd
    3adant1
    #
    @3
    @5
    @9
    @4
    @3
    @5
    @9
    @4
    wi
    @3
    @5
    wa
    #
    @7
    @8
    wceq
    #
    @8
    @7
    wcel
    #
    wo
    #
    wn
    #
    cA
    cB
    wceq
    #
    cB
    cA
    wcel
    #
    wo
    #
    wn
    #
    @9
    @4
    @16
    @23
    @19
    @16
    @21
    @17
    @22
    @18
    @21
    @17
    wi
    @16
    cA
    cB
    cC
    comu
    oveq2
    a1i
    @0
    @2
    @5
    @22
    @18
    wi
    @1
    cB
    cA
    cC
    nnmordi
    3adantl2
    orim12d
    con3d
    @16
    @7
    com
    wcel
    #
    @8
    com
    wcel
    #
    @9
    @20
    wb
    #
    @16
    @2
    @0
    @25
    @0
    @1
    @2
    @5
    simpl3
    #
    @0
    @1
    @2
    @5
    simpl1
    #
    cC
    cA
    nnmcl
    syl2anc
    @16
    @2
    @1
    @26
    @28
    @0
    @1
    @2
    @5
    simpl2
    #
    cC
    cB
    nnmcl
    syl2anc
    @25
    @7
    word
    @8
    word
    @27
    @26
    @7
    nnord
    @8
    nnord
    @7
    @8
    ordtri2
    syl2an
    syl2anc
    @16
    @0
    @1
    @4
    @24
    wb
    #
    @29
    @30
    @0
    cA
    word
    cB
    word
    @31
    @1
    cA
    nnord
    cB
    nnord
    cA
    cB
    ordtri2
    syl2an
    syl2anc
    3imtr4d
    ex
    com23
    mpdd
    @15
    jcad
    impbid
end
