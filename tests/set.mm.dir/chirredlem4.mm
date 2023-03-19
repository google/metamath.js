include "cv.mm"
include "cat.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "wo.mm"
include "wceq.mm"
include "ccm.mm"
include "wbr.mm"
include "cch.mm"
include "atelch.mm"
include "breq2.mm"
include "vtoclga.mm"
include "syl.mm"
include "atordi.mm"
include "mpdan.mm"
include "ad2antrl.mm"
include "chirredlem3.mm"
include "wi.mm"
include "ococi.mm"
include "sseq2i.mm"
include "biimpri.mm"
include "wb.mm"
include "chjcom.mm"
include "syl2an.mm"
include "sseq2d.mm"
include "anbi2d.mm"
include "ad2ant2r.mm"
include "choccli.mm"
include "cmcm3.mm"
include "mpan.mm"
include "mpbid.mm"
include "ex.mm"
include "sylbird.mm"
include "sylanr2.mm"
include "imp.mm"
include "ancom1s.mm"
include "orim12d.mm"
include "mpd.mm"

theorem chirredlem4
  let vx: setvar x
  let cA: class A
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  assume chirred.1: |- A e. CH
  assume chirred.2: |- ( x e. CH -> A C_H x )

  disjoint p q
  disjoint p r
  disjoint p x
  disjoint A p
  disjoint q r
  disjoint q x
  disjoint A q
  disjoint r x
  disjoint A r
  disjoint A x
  assert |- ( ( ( ( p e. HAtoms /\ p C_ A ) /\ ( q e. HAtoms /\ q C_ ( _|_ ` A ) ) ) /\ ( r e. HAtoms /\ r C_ ( p vH q ) ) ) -> ( r = p \/ r = q ) )

  proof
    vp
    cv
    #
    cat
    wcel
    #
    @0
    cA
    wss
    #
    wa
    #
    vq
    cv
    #
    cat
    wcel
    #
    @4
    cA
    cort
    cfv
    #
    wss
    #
    wa
    #
    wa
    #
    vr
    cv
    #
    cat
    wcel
    #
    @10
    @0
    @4
    chj
    co
    #
    wss
    #
    wa
    #
    wa
    #
    @10
    cA
    wss
    #
    @10
    @6
    wss
    #
    wo
    #
    @10
    @0
    wceq
    #
    @10
    @4
    wceq
    #
    wo
    @11
    @18
    @9
    @13
    @11
    cA
    @10
    ccm
    wbr
    #
    @18
    @11
    @10
    cch
    wcel
    @21
    @10
    atelch
    cA
    vx
    cv
    #
    ccm
    wbr
    #
    @21
    vx
    @10
    cch
    @22
    @10
    cA
    ccm
    breq2
    chirred.2
    vtoclga
    syl
    cA
    @10
    chirred.1
    atordi
    mpdan
    ad2antrl
    @15
    @16
    @19
    @17
    @20
    vx
    cA
    vr
    vq
    vp
    chirred.1
    chirred.2
    chirredlem3
    @8
    @3
    @14
    @17
    @20
    wi
    #
    @8
    @3
    wa
    @14
    @24
    @2
    @8
    @1
    @0
    @6
    cort
    cfv
    #
    wss
    #
    @14
    @24
    wi
    @26
    @2
    @25
    cA
    @0
    cA
    chirred.1
    ococi
    sseq2i
    biimpri
    @8
    @1
    @26
    wa
    wa
    #
    @14
    @11
    @10
    @4
    @0
    chj
    co
    #
    wss
    #
    wa
    #
    @24
    @5
    @1
    @30
    @14
    wb
    @7
    @26
    @5
    @1
    wa
    #
    @29
    @13
    @11
    @31
    @28
    @12
    @10
    @5
    @4
    cch
    wcel
    @0
    cch
    wcel
    @28
    @12
    wceq
    @1
    @4
    atelch
    @0
    atelch
    @4
    @0
    chjcom
    syl2an
    sseq2d
    anbi2d
    ad2ant2r
    @27
    @30
    @24
    vx
    @6
    vr
    vp
    vq
    cA
    chirred.1
    choccli
    @22
    cch
    wcel
    #
    @23
    @6
    @22
    ccm
    wbr
    #
    chirred.2
    cA
    cch
    wcel
    @32
    @23
    @33
    wb
    chirred.1
    cA
    @22
    cmcm3
    mpan
    mpbid
    chirredlem3
    ex
    sylbird
    sylanr2
    imp
    ancom1s
    orim12d
    mpd
end
