include "cv.mm"
include "cat.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "cch.mm"
include "atelch.mm"
include "c0h.mm"
include "cin.mm"
include "chirredlem2.mm"
include "oveq2d.mm"
include "adantr.mm"
include "chjcl.mm"
include "sylan.mm"
include "ad2ant2r.mm"
include "id.mm"
include "pjoml2.mm"
include "syl3an.mm"
include "3com12.mm"
include "3expb.mm"
include "eqtr3d.mm"
include "ineq2d.mm"
include "ccm.mm"
include "wbr.mm"
include "breq2.mm"
include "vtoclga.mm"
include "anim12i.mm"
include "fh1.mm"
include "mp3anl1.mm"
include "mpdan.mm"
include "ancoms.mm"
include "adantrr.mm"
include "adantll.mm"
include "3eqtr3d.mm"
include "sseqin2.mm"
include "biimpi.mm"
include "ad2antlr.mm"
include "adantl.mm"
include "incom.mm"
include "csh.mm"
include "chsh.mm"
include "chshii.mm"
include "orthin.mm"
include "sylancl.mm"
include "imp.mm"
include "syl5eq.mm"
include "oveq12d.mm"
include "ad2antrr.mm"
include "chj0.mm"
include "syl.mm"
include "ad3antrrr.mm"
include "exp44.mm"
include "com34.mm"
include "sylanr1.mm"
include "imp32.mm"

theorem chirredlem3
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
  assert |- ( ( ( ( p e. HAtoms /\ p C_ A ) /\ ( q e. HAtoms /\ q C_ ( _|_ ` A ) ) ) /\ ( r e. HAtoms /\ r C_ ( p vH q ) ) ) -> ( r C_ A -> r = p ) )

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
    wss
    #
    wa
    wa
    vr
    cv
    #
    cat
    wcel
    #
    @7
    @0
    @4
    chj
    co
    #
    wss
    #
    @7
    cA
    wss
    #
    @7
    @0
    wceq
    #
    wi
    #
    @5
    @3
    @4
    cch
    wcel
    #
    @6
    @8
    @10
    @13
    wi
    wi
    @4
    atelch
    @3
    @14
    @6
    wa
    #
    wa
    #
    @8
    @11
    @10
    @12
    @16
    @8
    @11
    @10
    @12
    @16
    @8
    @11
    wa
    #
    @10
    wa
    #
    wa
    #
    @7
    c0h
    chj
    co
    #
    @0
    c0h
    chj
    co
    #
    @7
    @0
    @19
    cA
    @7
    cin
    #
    cA
    @4
    cin
    #
    chj
    co
    #
    cA
    @0
    cin
    #
    @23
    chj
    co
    #
    @20
    @21
    @19
    cA
    @7
    @4
    chj
    co
    #
    cin
    #
    cA
    @9
    cin
    #
    @24
    @26
    @19
    @27
    @9
    cA
    @19
    @7
    @7
    cort
    cfv
    @9
    cin
    #
    chj
    co
    #
    @27
    @9
    @19
    @30
    @4
    @7
    chj
    cA
    vr
    vq
    vp
    chirred.1
    chirredlem2
    oveq2d
    @16
    @17
    @10
    @31
    @9
    wceq
    #
    @17
    @16
    @10
    @32
    @17
    @7
    cch
    wcel
    #
    @16
    @9
    cch
    wcel
    #
    @10
    @10
    @32
    @8
    @33
    @11
    @7
    atelch
    #
    adantr
    @1
    @14
    @34
    @2
    @6
    @1
    @0
    cch
    wcel
    #
    @14
    @34
    @0
    atelch
    #
    @0
    @4
    chjcl
    sylan
    ad2ant2r
    @10
    id
    @7
    @9
    pjoml2
    syl3an
    3com12
    3expb
    eqtr3d
    ineq2d
    @15
    @18
    @28
    @24
    wceq
    #
    @3
    @14
    @17
    @38
    @6
    @10
    @14
    @8
    @38
    @11
    @8
    @14
    @38
    @8
    @33
    @14
    @38
    @35
    @33
    @14
    wa
    cA
    @7
    ccm
    wbr
    #
    cA
    @4
    ccm
    wbr
    #
    wa
    #
    @38
    @33
    @39
    @14
    @40
    cA
    vx
    cv
    #
    ccm
    wbr
    #
    @39
    vx
    @7
    cch
    @42
    @7
    cA
    ccm
    breq2
    chirred.2
    vtoclga
    @43
    @40
    vx
    @4
    cch
    @42
    @4
    cA
    ccm
    breq2
    chirred.2
    vtoclga
    #
    anim12i
    cA
    cch
    wcel
    #
    @33
    @14
    @41
    @38
    chirred.1
    cA
    @7
    @4
    fh1
    mp3anl1
    mpdan
    sylan
    ancoms
    adantrr
    ad2ant2r
    adantll
    @16
    @29
    @26
    wceq
    #
    @18
    @1
    @14
    @46
    @2
    @6
    @1
    @36
    @14
    @46
    @37
    @36
    @14
    wa
    cA
    @0
    ccm
    wbr
    #
    @40
    wa
    #
    @46
    @36
    @47
    @14
    @40
    @43
    @47
    vx
    @0
    cch
    @42
    @0
    cA
    ccm
    breq2
    chirred.2
    vtoclga
    @44
    anim12i
    @45
    @36
    @14
    @48
    @46
    chirred.1
    cA
    @0
    @4
    fh1
    mp3anl1
    mpdan
    sylan
    ad2ant2r
    adantr
    3eqtr3d
    @19
    @22
    @7
    @23
    c0h
    chj
    @18
    @22
    @7
    wceq
    #
    @16
    @11
    @49
    @8
    @10
    @11
    @49
    @7
    cA
    sseqin2
    biimpi
    ad2antlr
    adantl
    @15
    @23
    c0h
    wceq
    @3
    @18
    @15
    @23
    @4
    cA
    cin
    #
    c0h
    cA
    @4
    incom
    @14
    @6
    @50
    c0h
    wceq
    #
    @14
    @4
    csh
    wcel
    cA
    csh
    wcel
    @6
    @51
    wi
    @4
    chsh
    cA
    chirred.1
    chshii
    @4
    cA
    orthin
    sylancl
    imp
    syl5eq
    ad2antlr
    #
    oveq12d
    @19
    @25
    @0
    @23
    c0h
    chj
    @3
    @25
    @0
    wceq
    #
    @15
    @18
    @2
    @53
    @1
    @2
    @53
    @0
    cA
    sseqin2
    biimpi
    adantl
    ad2antrr
    @52
    oveq12d
    3eqtr3d
    @18
    @20
    @7
    wceq
    #
    @16
    @8
    @54
    @11
    @10
    @8
    @33
    @54
    @35
    @7
    chj0
    syl
    ad2antrr
    adantl
    @1
    @21
    @0
    wceq
    #
    @2
    @15
    @18
    @1
    @36
    @55
    @37
    @0
    chj0
    syl
    ad3antrrr
    3eqtr3d
    exp44
    com34
    sylanr1
    imp32
end
