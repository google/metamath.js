include "cv.mm"
include "cmd.mm"
include "wbr.mm"
include "cdmd.mm"
include "wi.mm"
include "cch.mm"
include "wral.mm"
include "wa.mm"
include "cin.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "wcel.mm"
include "incom.mm"
include "sseq1i.mm"
include "biimpri.mm"
include "chjcom.mm"
include "mpan2.mm"
include "ineq1d.mm"
include "syl6eq.mm"
include "ad2antlr.mm"
include "w3a.mm"
include "a1i.mm"
include "id.mm"
include "3jca.mm"
include "inss2.mm"
include "ssid.mm"
include "pm3.2i.mm"
include "c0h.mm"
include "cif.mm"
include "sseq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "3anbi2d.mm"
include "breq1.mm"
include "imbi12d.mm"
include "h0elch.mm"
include "elimel.mm"
include "mdslmd4i.mm"
include "dedth.mm"
include "com12.mm"
include "mp3an3.mm"
include "imp.mm"
include "an32s.mm"
include "adantlll.mm"
include "breq2.mm"
include "rspccva.mm"
include "adantlr.mm"
include "adantr.mm"
include "mpd.mm"
include "simprr.mm"
include "dmdi.mm"
include "syl12anc.mm"
include "chincli.mm"
include "mpan.mm"
include "oveq2i.mm"
include "3eqtr2d.mm"
include "ex.mm"
include "sylani.mm"
include "ralrimiva.mm"
include "mdsl2bi.mm"
include "sylibr.mm"

theorem csmdsymi
  let cA: class A
  let cB: class B
  let vc: setvar c
  let vx: setvar x
  assume csmdsym.1: |- A e. CH
  assume csmdsym.2: |- B e. CH

  disjoint B c
  disjoint A x
  disjoint c x
  disjoint B x
  assert |- ( ( A. c e. CH ( c MH B -> B MH* c ) /\ A MH B ) -> B MH A )

  proof
    vc
    cv
    #
    cB
    cmd
    wbr
    #
    cB
    @0
    cdmd
    wbr
    #
    wi
    #
    vc
    cch
    wral
    #
    cA
    cB
    cmd
    wbr
    #
    wa
    #
    cB
    cA
    cin
    #
    vx
    cv
    #
    wss
    #
    @8
    cA
    wss
    #
    wa
    @8
    cB
    chj
    co
    #
    cA
    cin
    #
    @8
    @7
    chj
    co
    #
    wceq
    #
    wi
    #
    vx
    cch
    wral
    cB
    cA
    cmd
    wbr
    @6
    @15
    vx
    cch
    @9
    @6
    @8
    cch
    wcel
    #
    wa
    #
    cA
    cB
    cin
    #
    @8
    wss
    #
    @10
    @14
    @19
    @9
    @18
    @7
    @8
    cA
    cB
    incom
    #
    sseq1i
    biimpri
    @17
    @19
    @10
    wa
    #
    @14
    @17
    @21
    wa
    #
    @12
    cA
    cB
    @8
    chj
    co
    #
    cin
    #
    @18
    @8
    chj
    co
    #
    @13
    @16
    @12
    @24
    wceq
    @6
    @21
    @16
    @12
    @23
    cA
    cin
    @24
    @16
    @11
    @23
    cA
    @16
    cB
    cch
    wcel
    #
    @11
    @23
    wceq
    csmdsym.2
    @8
    cB
    chjcom
    mpan2
    ineq1d
    @23
    cA
    incom
    syl6eq
    ad2antlr
    @22
    @26
    @16
    cA
    cch
    wcel
    #
    w3a
    #
    cB
    @8
    cdmd
    wbr
    #
    @10
    @25
    @24
    wceq
    @16
    @28
    @6
    @21
    @16
    @26
    @16
    @27
    @26
    @16
    csmdsym.2
    a1i
    @16
    id
    @27
    @16
    csmdsym.1
    a1i
    3jca
    ad2antlr
    @22
    @8
    cB
    cmd
    wbr
    #
    @29
    @5
    @16
    @21
    @30
    @4
    @5
    @21
    @16
    @30
    @5
    @21
    wa
    @16
    @30
    @5
    @21
    @18
    cB
    wss
    #
    cB
    cB
    wss
    #
    wa
    #
    @16
    @30
    wi
    @31
    @32
    cA
    cB
    inss2
    cB
    ssid
    pm3.2i
    @16
    @5
    @21
    @33
    w3a
    #
    @30
    @16
    @34
    @30
    wi
    @5
    @18
    @16
    @8
    c0h
    cif
    #
    wss
    #
    @35
    cA
    wss
    #
    wa
    #
    @33
    w3a
    #
    @35
    cB
    cmd
    wbr
    #
    wi
    @8
    c0h
    @8
    @35
    wceq
    #
    @34
    @39
    @30
    @40
    @41
    @21
    @38
    @5
    @33
    @41
    @19
    @36
    @10
    @37
    @8
    @35
    @18
    sseq2
    @8
    @35
    cA
    sseq1
    anbi12d
    3anbi2d
    @8
    @35
    cB
    cmd
    breq1
    imbi12d
    cA
    cB
    @35
    cB
    csmdsym.1
    csmdsym.2
    @8
    c0h
    cch
    h0elch
    elimel
    csmdsym.2
    mdslmd4i
    dedth
    com12
    mp3an3
    imp
    an32s
    adantlll
    @17
    @30
    @29
    wi
    #
    @21
    @4
    @16
    @42
    @5
    @3
    @42
    vc
    @8
    cch
    @0
    @8
    wceq
    @1
    @30
    @2
    @29
    @0
    @8
    cB
    cmd
    breq1
    @0
    @8
    cB
    cdmd
    breq2
    imbi12d
    rspccva
    adantlr
    adantr
    mpd
    @17
    @19
    @10
    simprr
    cB
    @8
    cA
    dmdi
    syl12anc
    @16
    @25
    @13
    wceq
    @6
    @21
    @16
    @25
    @8
    @18
    chj
    co
    #
    @13
    @18
    cch
    wcel
    @16
    @25
    @43
    wceq
    cA
    cB
    csmdsym.1
    csmdsym.2
    chincli
    @18
    @8
    chjcom
    mpan
    @18
    @7
    @8
    chj
    @20
    oveq2i
    syl6eq
    ad2antlr
    3eqtr2d
    ex
    sylani
    ralrimiva
    vx
    cB
    cA
    csmdsym.2
    csmdsym.1
    mdsl2bi
    sylibr
end
