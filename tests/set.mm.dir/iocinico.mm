include "cxr.mm"
include "wcel.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cioc.mm"
include "co.mm"
include "cico.mm"
include "cin.mm"
include "csn.mm"
include "cicc.mm"
include "wss.mm"
include "cv.mm"
include "cab.mm"
include "df-in.mm"
include "cle.mm"
include "wb.mm"
include "elioc1.mm"
include "3adant3.mm"
include "3simpb.mm"
include "syl6bi.mm"
include "elico1.mm"
include "3adant1.mm"
include "3simpa.mm"
include "anim12d.mm"
include "simpll.mm"
include "simprr.mm"
include "simplr.mm"
include "3jca.mm"
include "syl6.mm"
include "elicc1.mm"
include "anidms.mm"
include "3ad2ant2.mm"
include "sylibrd.mm"
include "ss2abdv.mm"
include "syl5eqss.mm"
include "abid2.mm"
include "syl6sseq.mm"
include "adantr.mm"
include "wceq.mm"
include "iccid.mm"
include "sseqtrd.mm"
include "simpl2.mm"
include "simprl.mm"
include "xrleid.mm"
include "syl.mm"
include "mpbir3and.mm"
include "elind.mm"
include "snssd.mm"
include "eqssd.mm"

theorem iocinico
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) /\ ( A < B /\ B < C ) ) -> ( ( A (,] B ) i^i ( B [,) C ) ) = { B } )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    w3a
    #
    cA
    cB
    clt
    wbr
    #
    cB
    cC
    clt
    wbr
    #
    wa
    #
    wa
    #
    cA
    cB
    cioc
    co
    #
    cB
    cC
    cico
    co
    #
    cin
    #
    cB
    csn
    #
    @7
    @10
    cB
    cB
    cicc
    co
    #
    @11
    @3
    @10
    @12
    wss
    @6
    @3
    @10
    vx
    cv
    #
    @12
    wcel
    #
    vx
    cab
    #
    @12
    @3
    @10
    @13
    @8
    wcel
    #
    @13
    @9
    wcel
    #
    wa
    #
    vx
    cab
    @15
    vx
    @8
    @9
    df-in
    @3
    @18
    @14
    vx
    @3
    @18
    @13
    cxr
    wcel
    #
    cB
    @13
    cle
    wbr
    #
    @13
    cB
    cle
    wbr
    #
    w3a
    #
    @14
    @3
    @18
    @19
    @21
    wa
    #
    @19
    @20
    wa
    #
    wa
    #
    @22
    @3
    @16
    @23
    @17
    @24
    @3
    @16
    @19
    cA
    @13
    clt
    wbr
    #
    @21
    w3a
    #
    @23
    @0
    @1
    @16
    @27
    wb
    @2
    cA
    cB
    @13
    elioc1
    3adant3
    @19
    @26
    @21
    3simpb
    syl6bi
    @3
    @17
    @19
    @20
    @13
    cC
    clt
    wbr
    #
    w3a
    #
    @24
    @1
    @2
    @17
    @29
    wb
    @0
    cB
    cC
    @13
    elico1
    3adant1
    @19
    @20
    @28
    3simpa
    syl6bi
    anim12d
    @25
    @19
    @20
    @21
    @19
    @21
    @24
    simpll
    @23
    @19
    @20
    simprr
    @19
    @21
    @24
    simplr
    3jca
    syl6
    @1
    @0
    @14
    @22
    wb
    #
    @2
    @1
    @30
    cB
    cB
    @13
    elicc1
    anidms
    3ad2ant2
    sylibrd
    ss2abdv
    syl5eqss
    vx
    @12
    abid2
    syl6sseq
    adantr
    @3
    @12
    @11
    wceq
    #
    @6
    @1
    @0
    @31
    @2
    cB
    iccid
    3ad2ant2
    adantr
    sseqtrd
    @7
    cB
    @10
    @7
    @8
    @9
    cB
    @7
    cB
    @8
    wcel
    #
    @1
    @4
    cB
    cB
    cle
    wbr
    #
    @0
    @1
    @2
    @6
    simpl2
    #
    @3
    @4
    @5
    simprl
    @7
    @1
    @33
    @34
    cB
    xrleid
    syl
    #
    @3
    @32
    @1
    @4
    @33
    w3a
    wb
    #
    @6
    @0
    @1
    @36
    @2
    cA
    cB
    cB
    elioc1
    3adant3
    adantr
    mpbir3and
    @7
    cB
    @9
    wcel
    #
    @1
    @33
    @5
    @34
    @35
    @3
    @4
    @5
    simprr
    @3
    @37
    @1
    @33
    @5
    w3a
    wb
    #
    @6
    @1
    @2
    @38
    @0
    cB
    cC
    cB
    elico1
    3adant1
    adantr
    mpbir3and
    elind
    snssd
    eqssd
end
