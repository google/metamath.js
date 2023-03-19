include "cv.mm"
include "cat.mm"
include "wcel.mm"
include "cch.mm"
include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "c0h.mm"
include "wceq.mm"
include "wi.mm"
include "atelch.mm"
include "wb.mm"
include "chsscon3.mm"
include "mpan2.mm"
include "biimpa.mm"
include "sylan.mm"
include "sstr2.mm"
include "syl5.mm"
include "wn.mm"
include "atne0.mm"
include "neneqd.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "choccl.mm"
include "syl.mm"
include "chlej1.mm"
include "3exp1.mm"
include "syl5com.mm"
include "imp42.mm"
include "adantllr.mm"
include "adantlr.mm"
include "sstrd.mm"
include "chlejb2.mm"
include "ancoms.mm"
include "sylanl1.mm"
include "an32s.mm"
include "adantrl.mm"
include "ad2antrr.mm"
include "sseqtrd.mm"
include "ex.mm"
include "chssoc.mm"
include "biimpd.mm"
include "syld.mm"
include "mtod.mm"
include "sylanr1.mm"
include "atnssm0.mm"
include "incom.mm"
include "eqeq1i.mm"
include "syl6bb.mm"
include "ad2ant2r.mm"
include "sylibd.mm"
include "exp43.mm"
include "adantr.mm"
include "sylcom.mm"
include "com4t.mm"
include "impd.mm"
include "imp43.mm"

theorem chirredlem1
  let cA: class A
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vx: setvar x
  assume chirred.1: |- A e. CH

  disjoint p q
  disjoint p r
  disjoint A p
  disjoint q r
  disjoint A q
  disjoint A r
  disjoint p x
  disjoint q x
  disjoint r x
  disjoint A x
  assert |- ( ( ( p e. HAtoms /\ ( q e. CH /\ q C_ ( _|_ ` A ) ) ) /\ ( ( r e. HAtoms /\ r C_ A ) /\ r C_ ( p vH q ) ) ) -> ( p i^i ( _|_ ` r ) ) = 0H )

  proof
    vp
    cv
    #
    cat
    wcel
    #
    vq
    cv
    #
    cch
    wcel
    #
    @2
    cA
    cort
    cfv
    #
    wss
    #
    wa
    vr
    cv
    #
    cat
    wcel
    #
    @6
    cA
    wss
    #
    wa
    #
    @6
    @0
    @2
    chj
    co
    #
    wss
    #
    @0
    @6
    cort
    cfv
    #
    cin
    #
    c0h
    wceq
    #
    @1
    @3
    @5
    @9
    @11
    @14
    wi
    #
    wi
    @5
    @9
    @1
    @3
    @15
    @5
    @9
    @2
    @12
    wss
    #
    @1
    @3
    @15
    wi
    wi
    #
    @9
    @4
    @12
    wss
    #
    @5
    @16
    @7
    @6
    cch
    wcel
    #
    @8
    @18
    @6
    atelch
    #
    @19
    @8
    @18
    @19
    cA
    cch
    wcel
    @8
    @18
    wb
    chirred.1
    @6
    cA
    chsscon3
    mpan2
    biimpa
    sylan
    @2
    @4
    @12
    sstr2
    syl5
    @7
    @16
    @17
    wi
    @8
    @7
    @16
    @1
    @3
    @15
    @7
    @16
    wa
    #
    @1
    @3
    wa
    wa
    @11
    @0
    @12
    wss
    #
    wn
    #
    @14
    @1
    @21
    @0
    cch
    wcel
    #
    @3
    @11
    @23
    wi
    @0
    atelch
    @21
    @24
    @3
    wa
    #
    wa
    #
    @11
    @23
    @26
    @11
    wa
    #
    @22
    @6
    c0h
    wceq
    #
    @7
    @28
    wn
    @16
    @25
    @11
    @7
    @6
    c0h
    @6
    atne0
    neneqd
    ad3antrrr
    @27
    @22
    @6
    @12
    wss
    #
    @28
    @27
    @22
    @29
    @27
    @22
    wa
    #
    @6
    @12
    @2
    chj
    co
    #
    @12
    @30
    @6
    @10
    @31
    @26
    @11
    @22
    simplr
    @26
    @22
    @10
    @31
    wss
    #
    @11
    @7
    @25
    @22
    @32
    @16
    @7
    @24
    @3
    @22
    @32
    @7
    @12
    cch
    wcel
    #
    @24
    @3
    @22
    @32
    wi
    wi
    @7
    @19
    @33
    @20
    @6
    choccl
    syl
    #
    @24
    @33
    @3
    @22
    @32
    @0
    @12
    @2
    chlej1
    3exp1
    syl5com
    imp42
    adantllr
    adantlr
    sstrd
    @26
    @31
    @12
    wceq
    #
    @11
    @22
    @21
    @3
    @35
    @24
    @7
    @3
    @16
    @35
    @7
    @33
    @3
    @16
    @35
    @34
    @33
    @3
    wa
    @16
    @35
    @3
    @33
    @16
    @35
    wb
    @2
    @12
    chlejb2
    ancoms
    biimpa
    sylanl1
    an32s
    adantrl
    ad2antrr
    sseqtrd
    ex
    @7
    @29
    @28
    wi
    #
    @16
    @25
    @11
    @7
    @19
    @36
    @20
    @19
    @29
    @28
    @6
    chssoc
    biimpd
    syl
    ad3antrrr
    syld
    mtod
    ex
    sylanr1
    @7
    @1
    @23
    @14
    wb
    #
    @16
    @3
    @7
    @33
    @1
    @37
    @34
    @33
    @1
    wa
    @23
    @12
    @0
    cin
    #
    c0h
    wceq
    @14
    @12
    @0
    atnssm0
    @38
    @13
    c0h
    @12
    @0
    incom
    eqeq1i
    syl6bb
    sylan
    ad2ant2r
    sylibd
    exp43
    adantr
    sylcom
    com4t
    impd
    imp43
end
