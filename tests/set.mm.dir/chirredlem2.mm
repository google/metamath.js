include "cv.mm"
include "cat.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cch.mm"
include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "atelch.mm"
include "chjcom.mm"
include "sylan.mm"
include "ad2ant2r.mm"
include "adantr.mm"
include "ineq2d.mm"
include "w3a.mm"
include "ccm.mm"
include "wbr.mm"
include "choccl.mm"
include "syl.mm"
include "id.mm"
include "3anim123i.mm"
include "3com13.mm"
include "3expa.mm"
include "adantllr.mm"
include "adantlrr.mm"
include "adantrr.mm"
include "simpll.mm"
include "ad2antrl.mm"
include "wb.mm"
include "chsscon3.mm"
include "sylancl.mm"
include "biimpa.mm"
include "sstr.mm"
include "sylan2.mm"
include "adantll.mm"
include "lecm.mm"
include "syl3anc.mm"
include "ad2ant2lr.mm"
include "mpan2.mm"
include "an12s.mm"
include "ancom2s.mm"
include "wi.mm"
include "syl3an2.mm"
include "3expia.mm"
include "cmcm2.mm"
include "sylibrd.mm"
include "mpd.mm"
include "sylanl2.mm"
include "ancom1s.mm"
include "an4s.mm"
include "fh2.mm"
include "syl12anc.mm"
include "c0h.mm"
include "sseqin2.mm"
include "sylib.mm"
include "incom.mm"
include "chirredlem1.mm"
include "syl5eq.mm"
include "oveq12d.mm"
include "chj0.mm"
include "ad2antlr.mm"
include "eqtrd.mm"
include "3eqtrd.mm"

theorem chirredlem2
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
  assert |- ( ( ( ( p e. HAtoms /\ p C_ A ) /\ ( q e. CH /\ q C_ ( _|_ ` A ) ) ) /\ ( ( r e. HAtoms /\ r C_ A ) /\ r C_ ( p vH q ) ) ) -> ( ( _|_ ` r ) i^i ( p vH q ) ) = q )

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
    cch
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
    cA
    wss
    #
    wa
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
    cort
    cfv
    #
    @14
    cin
    @18
    @4
    @0
    chj
    co
    #
    cin
    #
    @18
    @4
    cin
    #
    @18
    @0
    cin
    #
    chj
    co
    #
    @4
    @17
    @14
    @19
    @18
    @9
    @14
    @19
    wceq
    #
    @16
    @1
    @5
    @24
    @2
    @7
    @1
    @0
    cch
    wcel
    #
    @5
    @24
    @0
    atelch
    #
    @0
    @4
    chjcom
    sylan
    ad2ant2r
    adantr
    ineq2d
    @17
    @18
    cch
    wcel
    #
    @5
    @25
    w3a
    #
    @4
    @18
    ccm
    wbr
    #
    @4
    @0
    ccm
    wbr
    #
    @20
    @23
    wceq
    @9
    @13
    @28
    @15
    @9
    @11
    @28
    @12
    @3
    @5
    @11
    @28
    @7
    @1
    @5
    @11
    @28
    @2
    @1
    @5
    @11
    @28
    @11
    @5
    @1
    @28
    @11
    @27
    @5
    @5
    @1
    @25
    @11
    @10
    cch
    wcel
    #
    @27
    @10
    atelch
    #
    @10
    choccl
    syl
    #
    @5
    id
    @26
    3anim123i
    3com13
    3expa
    adantllr
    adantlrr
    adantrr
    adantrr
    @8
    @13
    @29
    @3
    @15
    @8
    @13
    wa
    #
    @5
    @27
    @4
    @18
    wss
    #
    @29
    @5
    @7
    @13
    simpll
    @11
    @27
    @8
    @12
    @33
    ad2antrl
    @7
    @13
    @35
    @5
    @13
    @7
    @6
    @18
    wss
    #
    @35
    @11
    @12
    @36
    @11
    @31
    cA
    cch
    wcel
    #
    @12
    @36
    wb
    @32
    chirred.1
    @10
    cA
    chsscon3
    sylancl
    biimpa
    @4
    @6
    @18
    sstr
    sylan2
    adantll
    #
    @4
    @18
    lecm
    syl3anc
    ad2ant2lr
    @9
    @30
    @16
    @1
    @5
    @2
    @7
    @30
    @5
    @1
    @2
    @7
    wa
    #
    @30
    @1
    @5
    @25
    @39
    @30
    @26
    @5
    @25
    wa
    #
    @39
    wa
    @4
    @0
    cort
    cfv
    #
    wss
    #
    @30
    @25
    @39
    @42
    @5
    @25
    @7
    @2
    @42
    @7
    @25
    @2
    @42
    @25
    @2
    wa
    @7
    @6
    @41
    wss
    #
    @42
    @25
    @2
    @43
    @25
    @37
    @2
    @43
    wb
    chirred.1
    @0
    cA
    chsscon3
    mpan2
    biimpa
    @4
    @6
    @41
    sstr
    sylan2
    an12s
    ancom2s
    adantll
    @40
    @42
    @30
    wi
    @39
    @40
    @42
    @4
    @41
    ccm
    wbr
    #
    @30
    @5
    @25
    @42
    @44
    @25
    @5
    @41
    cch
    wcel
    @42
    @44
    @0
    choccl
    @4
    @41
    lecm
    syl3an2
    3expia
    @4
    @0
    cmcm2
    sylibrd
    adantr
    mpd
    sylanl2
    ancom1s
    an4s
    adantr
    @18
    @4
    @0
    fh2
    syl12anc
    @17
    @23
    @4
    c0h
    chj
    co
    #
    @4
    @17
    @21
    @4
    @22
    c0h
    chj
    @8
    @13
    @21
    @4
    wceq
    #
    @3
    @15
    @34
    @35
    @46
    @38
    @4
    @18
    sseqin2
    sylib
    ad2ant2lr
    @17
    @22
    @0
    @18
    cin
    #
    c0h
    @18
    @0
    incom
    @1
    @8
    @16
    @47
    c0h
    wceq
    @2
    cA
    vr
    vq
    vp
    chirred.1
    chirredlem1
    adantllr
    syl5eq
    oveq12d
    @8
    @45
    @4
    wceq
    #
    @3
    @16
    @5
    @48
    @7
    @4
    chj0
    adantr
    ad2antlr
    eqtrd
    3eqtrd
end
