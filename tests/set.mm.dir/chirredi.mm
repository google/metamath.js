include "c0h.mm"
include "wceq.mm"
include "cort.mm"
include "cfv.mm"
include "wo.mm"
include "chil.mm"
include "eqid.mm"
include "wn.mm"
include "wne.mm"
include "wa.mm"
include "ioran.mm"
include "df-ne.mm"
include "anbi12i.mm"
include "bitr4i.mm"
include "cv.mm"
include "wss.mm"
include "cat.mm"
include "wrex.mm"
include "hatomici.mm"
include "choccli.mm"
include "anim12i.mm"
include "reeanv.mm"
include "sylibr.mm"
include "wcel.mm"
include "chj.mm"
include "co.mm"
include "w3a.mm"
include "simpll.mm"
include "simprl.mm"
include "cch.mm"
include "wb.mm"
include "atelch.mm"
include "chsscon3.mm"
include "sylancl.mm"
include "biimpa.mm"
include "sstr.mm"
include "sylan2.mm"
include "ancoms.mm"
include "atne0.mm"
include "adantr.mm"
include "sseq1.mm"
include "bicomd.mm"
include "chssoc.mm"
include "syl.mm"
include "sylan9bbr.mm"
include "an32s.mm"
include "ex.mm"
include "necon3d.mm"
include "mpd.mm"
include "adantlr.mm"
include "syldan.mm"
include "adantrl.mm"
include "superpos.mm"
include "syl3anc.mm"
include "df-3an.mm"
include "neanior.mm"
include "anbi1i.mm"
include "bitri.mm"
include "wi.mm"
include "chirredlem4.mm"
include "anassrs.mm"
include "pm2.24d.mm"
include "com23.mm"
include "impd.mm"
include "syl5bi.mm"
include "rexlimdva.mm"
include "an4s.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "mt4.mm"
include "fveq2.mm"
include "ococi.mm"
include "choc0.mm"
include "3eqtr3g.mm"
include "orim2i.mm"
include "ax-mp.mm"

theorem chirredi
  let vx: setvar x
  let cA: class A
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  assume chirred.1: |- A e. CH
  assume chirred.2: |- ( x e. CH -> A C_H x )

  disjoint A x
  disjoint p q
  disjoint p r
  disjoint p x
  disjoint A p
  disjoint q r
  disjoint q x
  disjoint A q
  disjoint r x
  disjoint A r
  assert |- ( A = 0H \/ A = ~H )

  proof
    cA
    c0h
    wceq
    #
    cA
    cort
    cfv
    #
    c0h
    wceq
    #
    wo
    #
    @0
    cA
    chil
    wceq
    #
    wo
    c0h
    c0h
    wceq
    #
    @3
    c0h
    eqid
    @3
    wn
    #
    cA
    c0h
    wne
    #
    @1
    c0h
    wne
    #
    wa
    #
    @5
    wn
    #
    @6
    @0
    wn
    #
    @2
    wn
    #
    wa
    @9
    @0
    @2
    ioran
    @7
    @11
    @8
    @12
    cA
    c0h
    df-ne
    @1
    c0h
    df-ne
    anbi12i
    bitr4i
    @9
    vp
    cv
    #
    cA
    wss
    #
    vq
    cv
    #
    @1
    wss
    #
    wa
    #
    vq
    cat
    wrex
    vp
    cat
    wrex
    #
    @10
    @9
    @14
    vp
    cat
    wrex
    #
    @16
    vq
    cat
    wrex
    #
    wa
    @18
    @7
    @19
    @8
    @20
    vp
    cA
    chirred.1
    hatomici
    vq
    @1
    cA
    chirred.1
    choccli
    hatomici
    anim12i
    @14
    @16
    vp
    vq
    cat
    cat
    reeanv
    sylibr
    @17
    @10
    vp
    vq
    cat
    cat
    @13
    cat
    wcel
    #
    @15
    cat
    wcel
    #
    wa
    @17
    @10
    @21
    @14
    @22
    @16
    @10
    @21
    @14
    wa
    #
    @22
    @16
    wa
    #
    wa
    #
    vr
    cv
    #
    @13
    wne
    #
    @26
    @15
    wne
    #
    @26
    @13
    @15
    chj
    co
    wss
    #
    w3a
    #
    vr
    cat
    wrex
    #
    @10
    @25
    @21
    @22
    @13
    @15
    wne
    #
    @31
    @21
    @14
    @24
    simpll
    @23
    @22
    @16
    simprl
    @23
    @16
    @32
    @22
    @23
    @16
    @15
    @13
    cort
    cfv
    #
    wss
    #
    @32
    @16
    @23
    @34
    @23
    @16
    @1
    @33
    wss
    #
    @34
    @21
    @14
    @35
    @21
    @13
    cch
    wcel
    #
    cA
    cch
    wcel
    @14
    @35
    wb
    @13
    atelch
    #
    chirred.1
    @13
    cA
    chsscon3
    sylancl
    biimpa
    @15
    @1
    @33
    sstr
    sylan2
    ancoms
    @21
    @34
    @32
    @14
    @21
    @34
    wa
    #
    @13
    c0h
    wne
    #
    @32
    @21
    @39
    @34
    @13
    atne0
    adantr
    @38
    @13
    @15
    @13
    c0h
    @38
    @13
    @15
    wceq
    #
    @13
    c0h
    wceq
    #
    @21
    @40
    @34
    @41
    @21
    @40
    wa
    @34
    @41
    @40
    @34
    @13
    @33
    wss
    #
    @21
    @41
    @40
    @42
    @34
    @13
    @15
    @33
    sseq1
    bicomd
    @21
    @36
    @42
    @41
    wb
    @37
    @13
    chssoc
    syl
    sylan9bbr
    biimpa
    an32s
    ex
    necon3d
    mpd
    adantlr
    syldan
    adantrl
    vr
    @13
    @15
    superpos
    syl3anc
    @25
    @30
    @10
    vr
    cat
    @30
    @26
    @13
    wceq
    @26
    @15
    wceq
    wo
    #
    wn
    #
    @29
    wa
    #
    @25
    @26
    cat
    wcel
    #
    wa
    #
    @10
    @30
    @27
    @28
    wa
    #
    @29
    wa
    @45
    @27
    @28
    @29
    df-3an
    @48
    @44
    @29
    @26
    @13
    @26
    @15
    neanior
    anbi1i
    bitri
    @47
    @44
    @29
    @10
    @47
    @29
    @44
    @10
    @47
    @29
    @44
    @10
    wi
    @47
    @29
    wa
    @43
    @10
    @25
    @46
    @29
    @43
    vx
    cA
    vr
    vq
    vp
    chirred.1
    chirred.2
    chirredlem4
    anassrs
    pm2.24d
    ex
    com23
    impd
    syl5bi
    rexlimdva
    mpd
    an4s
    ex
    rexlimivv
    syl
    sylbi
    mt4
    @2
    @4
    @0
    @2
    @1
    cort
    cfv
    c0h
    cort
    cfv
    cA
    chil
    @1
    c0h
    cort
    fveq2
    cA
    chirred.1
    ococi
    choc0
    3eqtr3g
    orim2i
    ax-mp
end
