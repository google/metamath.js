include "cv.mm"
include "cch.mm"
include "wcel.mm"
include "cin.mm"
include "wss.mm"
include "wa.mm"
include "cdmd.mm"
include "wbr.mm"
include "chj.mm"
include "co.mm"
include "chub2.mm"
include "mpan2.mm"
include "syl6sseqr.mm"
include "chjcomi.mm"
include "sseq2i.mm"
include "biimpi.mm"
include "anim12i.mm"
include "ssin.mm"
include "sylib.mm"
include "ad2ant2rl.mm"
include "wceq.mm"
include "chjcl.mm"
include "mpan.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "chub1.mm"
include "anim2i.mm"
include "ancoms.mm"
include "dmdi.mm"
include "mp3anl1.mm"
include "mpanl1.mm"
include "syl2anc.mm"
include "adantlr.mm"
include "incom.mm"
include "oveq1i.mm"
include "wb.mm"
include "chincl.mm"
include "chlejb1.mm"
include "3syl.mm"
include "biimpa.mm"
include "syl5eq.mm"
include "eqtr3d.mm"
include "adantrr.mm"
include "sseqtrd.mm"

theorem mdsymlem1
  let cA: class A
  let cB: class B
  let cC: class C
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vc: setvar c
  assume mdsymlem1.1: |- A e. CH
  assume mdsymlem1.2: |- B e. CH
  assume mdsymlem1.3: |- C = ( A vH p )

  disjoint A p
  disjoint B p
  disjoint q r
  disjoint C q
  disjoint C r
  disjoint c p
  disjoint c q
  disjoint c r
  disjoint A c
  disjoint p q
  disjoint p r
  disjoint A q
  disjoint A r
  disjoint B c
  disjoint B q
  disjoint B r
  assert |- ( ( ( p e. CH /\ ( B i^i C ) C_ A ) /\ ( B MH* A /\ p C_ ( A vH B ) ) ) -> p C_ A )

  proof
    vp
    cv
    #
    cch
    wcel
    #
    cB
    cC
    cin
    #
    cA
    wss
    #
    wa
    #
    cB
    cA
    cdmd
    wbr
    #
    @0
    cA
    cB
    chj
    co
    #
    wss
    #
    wa
    wa
    @0
    cC
    cB
    cA
    chj
    co
    #
    cin
    #
    cA
    @1
    @7
    @0
    @9
    wss
    #
    @3
    @5
    @1
    @7
    wa
    @0
    cC
    wss
    #
    @0
    @8
    wss
    #
    wa
    @10
    @1
    @11
    @7
    @12
    @1
    @0
    cA
    @0
    chj
    co
    #
    cC
    @1
    cA
    cch
    wcel
    #
    @0
    @13
    wss
    mdsymlem1.1
    @0
    cA
    chub2
    mpan2
    mdsymlem1.3
    syl6sseqr
    @7
    @12
    @6
    @8
    @0
    cA
    cB
    mdsymlem1.1
    mdsymlem1.2
    chjcomi
    sseq2i
    biimpi
    anim12i
    @0
    cC
    @8
    ssin
    sylib
    ad2ant2rl
    @4
    @5
    @9
    cA
    wceq
    @7
    @4
    @5
    wa
    cC
    cB
    cin
    #
    cA
    chj
    co
    #
    @9
    cA
    @1
    @5
    @16
    @9
    wceq
    #
    @3
    @1
    @5
    wa
    cC
    cch
    wcel
    #
    @5
    cA
    cC
    wss
    #
    wa
    #
    @17
    @1
    @18
    @5
    @1
    cC
    @13
    cch
    mdsymlem1.3
    @14
    @1
    @13
    cch
    wcel
    mdsymlem1.1
    cA
    @0
    chjcl
    mpan
    syl5eqel
    #
    adantr
    @5
    @1
    @20
    @1
    @19
    @5
    @1
    cA
    @13
    cC
    @14
    @1
    cA
    @13
    wss
    mdsymlem1.1
    cA
    @0
    chub1
    mpan
    mdsymlem1.3
    syl6sseqr
    anim2i
    ancoms
    @14
    @18
    @20
    @17
    mdsymlem1.1
    cB
    cch
    wcel
    #
    @14
    @18
    @20
    @17
    mdsymlem1.2
    cB
    cA
    cC
    dmdi
    mp3anl1
    mpanl1
    syl2anc
    adantlr
    @4
    @16
    cA
    wceq
    @5
    @4
    @16
    @2
    cA
    chj
    co
    #
    cA
    @15
    @2
    cA
    chj
    cC
    cB
    incom
    oveq1i
    @1
    @3
    @23
    cA
    wceq
    #
    @1
    @18
    @2
    cch
    wcel
    #
    @3
    @24
    wb
    #
    @21
    @22
    @18
    @25
    mdsymlem1.2
    cB
    cC
    chincl
    mpan
    @25
    @14
    @26
    mdsymlem1.1
    @2
    cA
    chlejb1
    mpan2
    3syl
    biimpa
    syl5eq
    adantr
    eqtr3d
    adantrr
    sseqtrd
end
