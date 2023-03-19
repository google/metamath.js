include "c0h.mm"
include "wne.mm"
include "cv.mm"
include "wss.mm"
include "cat.mm"
include "wrex.mm"
include "wcel.mm"
include "cin.mm"
include "wa.mm"
include "cdmd.mm"
include "wbr.mm"
include "chj.mm"
include "co.mm"
include "hatomici.mm"
include "simplll.mm"
include "cch.mm"
include "atelch.mm"
include "chub1.mm"
include "syl2an.mm"
include "adantlr.mm"
include "mdsymlem1.mm"
include "sylanl1.mm"
include "adantr.mm"
include "jca.mm"
include "anim1i.mm"
include "anass.mm"
include "sylib.mm"
include "anasss.mm"
include "weq.mm"
include "oveq1.mm"
include "sseq2d.mm"
include "sseq1.mm"
include "anbi1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "exp32.mm"
include "reximdvai.mm"
include "syl5.mm"

theorem mdsymlem2
  let cA: class A
  let cB: class B
  let cC: class C
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vc: setvar c
  assume mdsymlem1.1: |- A e. CH
  assume mdsymlem1.2: |- B e. CH
  assume mdsymlem1.3: |- C = ( A vH p )

  disjoint q r
  disjoint C q
  disjoint C r
  disjoint p q
  disjoint p r
  disjoint A p
  disjoint A q
  disjoint A r
  disjoint B p
  disjoint B q
  disjoint B r
  disjoint c p
  disjoint c q
  disjoint c r
  disjoint A c
  disjoint B c
  assert |- ( ( ( p e. HAtoms /\ ( B i^i C ) C_ A ) /\ ( B MH* A /\ p C_ ( A vH B ) ) ) -> ( B =/= 0H -> E. r e. HAtoms E. q e. HAtoms ( p C_ ( q vH r ) /\ ( q C_ A /\ r C_ B ) ) ) )

  proof
    cB
    c0h
    wne
    vr
    cv
    #
    cB
    wss
    #
    vr
    cat
    wrex
    vp
    cv
    #
    cat
    wcel
    #
    cB
    cC
    cin
    cA
    wss
    #
    wa
    #
    cB
    cA
    cdmd
    wbr
    @2
    cA
    cB
    chj
    co
    wss
    wa
    #
    wa
    #
    @2
    vq
    cv
    #
    @0
    chj
    co
    #
    wss
    #
    @8
    cA
    wss
    #
    @1
    wa
    #
    wa
    #
    vq
    cat
    wrex
    #
    vr
    cat
    wrex
    vr
    cB
    mdsymlem1.2
    hatomici
    @7
    @1
    @14
    vr
    cat
    @7
    @0
    cat
    wcel
    #
    @1
    @14
    @7
    @15
    @1
    wa
    #
    wa
    @3
    @2
    @2
    @0
    chj
    co
    #
    wss
    #
    @2
    cA
    wss
    #
    @1
    wa
    #
    wa
    #
    @14
    @3
    @4
    @6
    @16
    simplll
    @7
    @15
    @1
    @21
    @7
    @15
    wa
    #
    @1
    wa
    @18
    @19
    wa
    #
    @1
    wa
    @21
    @22
    @23
    @1
    @22
    @18
    @19
    @5
    @15
    @18
    @6
    @3
    @15
    @18
    @4
    @3
    @2
    cch
    wcel
    #
    @0
    cch
    wcel
    @18
    @15
    @2
    atelch
    #
    @0
    atelch
    @2
    @0
    chub1
    syl2an
    adantlr
    adantlr
    @7
    @19
    @15
    @3
    @24
    @4
    @6
    @19
    @25
    cA
    cB
    cC
    vp
    mdsymlem1.1
    mdsymlem1.2
    mdsymlem1.3
    mdsymlem1
    sylanl1
    adantr
    jca
    anim1i
    @18
    @19
    @1
    anass
    sylib
    anasss
    @13
    @21
    vq
    @2
    cat
    vq
    vp
    weq
    #
    @10
    @18
    @12
    @20
    @26
    @9
    @17
    @2
    @8
    @2
    @0
    chj
    oveq1
    sseq2d
    @26
    @11
    @19
    @1
    @8
    @2
    cA
    sseq1
    anbi1d
    anbi12d
    rspcev
    syl2anc
    exp32
    reximdvai
    syl5
end
