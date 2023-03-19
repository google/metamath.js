include "c0h.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "chj.mm"
include "co.mm"
include "wss.mm"
include "cat.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cdmd.mm"
include "wbr.mm"
include "wb.mm"
include "chjcomi.mm"
include "sseq2i.mm"
include "wcel.mm"
include "cch.mm"
include "wceq.mm"
include "atelch.mm"
include "chjcom.mm"
include "syl2an.mm"
include "sseq2d.mm"
include "ancom.mm"
include "a1i.mm"
include "anbi12d.mm"
include "2rexbiia.mm"
include "rexcom.mm"
include "bitri.mm"
include "imbi12i.mm"
include "ralbii.mm"
include "mdsymlem7.mm"
include "eqid.mm"
include "ancoms.mm"
include "3bitr4d.mm"

theorem mdsymlem8
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
  assert |- ( ( A =/= 0H /\ B =/= 0H ) -> ( B MH* A <-> A MH* B ) )

  proof
    cA
    c0h
    wne
    #
    cB
    c0h
    wne
    #
    wa
    #
    vp
    cv
    #
    cA
    cB
    chj
    co
    #
    wss
    #
    @3
    vq
    cv
    #
    vr
    cv
    #
    chj
    co
    #
    wss
    #
    @6
    cA
    wss
    #
    @7
    cB
    wss
    #
    wa
    #
    wa
    #
    vr
    cat
    wrex
    vq
    cat
    wrex
    #
    wi
    #
    vp
    cat
    wral
    #
    @3
    cB
    cA
    chj
    co
    #
    wss
    #
    @3
    @7
    @6
    chj
    co
    #
    wss
    #
    @11
    @10
    wa
    #
    wa
    #
    vq
    cat
    wrex
    vr
    cat
    wrex
    #
    wi
    #
    vp
    cat
    wral
    #
    cB
    cA
    cdmd
    wbr
    cA
    cB
    cdmd
    wbr
    #
    @16
    @25
    wb
    @2
    @15
    @24
    vp
    cat
    @5
    @18
    @14
    @23
    @4
    @17
    @3
    cA
    cB
    mdsymlem1.1
    mdsymlem1.2
    chjcomi
    sseq2i
    @14
    @22
    vr
    cat
    wrex
    vq
    cat
    wrex
    @23
    @13
    @22
    vq
    vr
    cat
    cat
    @6
    cat
    wcel
    #
    @7
    cat
    wcel
    #
    wa
    #
    @9
    @20
    @12
    @21
    @29
    @8
    @19
    @3
    @27
    @6
    cch
    wcel
    @7
    cch
    wcel
    @8
    @19
    wceq
    @28
    @6
    atelch
    @7
    atelch
    @6
    @7
    chjcom
    syl2an
    sseq2d
    @12
    @21
    wb
    @29
    @10
    @11
    ancom
    a1i
    anbi12d
    2rexbiia
    @22
    vq
    vr
    cat
    cat
    rexcom
    bitri
    imbi12i
    ralbii
    a1i
    cA
    cB
    cC
    vr
    vq
    vp
    mdsymlem1.1
    mdsymlem1.2
    mdsymlem1.3
    mdsymlem7
    @1
    @0
    @26
    @25
    wb
    cB
    cA
    cB
    @3
    chj
    co
    #
    vq
    vr
    vp
    mdsymlem1.2
    mdsymlem1.1
    @30
    eqid
    mdsymlem7
    ancoms
    3bitr4d
end
