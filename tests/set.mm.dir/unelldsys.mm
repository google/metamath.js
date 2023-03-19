include "cun.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "uneq1.mm"
include "adantl.mm"
include "uncom.mm"
include "un0.mm"
include "eqtr3i.mm"
include "syl6eq.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "wne.mm"
include "cpr.mm"
include "cuni.mm"
include "uniprg.mm"
include "syl2anc.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wdisj.mm"
include "prct.mm"
include "cin.mm"
include "wb.mm"
include "wex.mm"
include "n0.mm"
include "biimpi.mm"
include "wn.mm"
include "disjel.mm"
include "sylan.mm"
include "nelne1.mm"
include "adantll.mm"
include "mpdan.mm"
include "adantlr.mm"
include "exlimddv.mm"
include "id.mm"
include "disjprg.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "wi.mm"
include "cpw.mm"
include "breq1.mm"
include "disjeq1.mm"
include "anbi12d.mm"
include "unieq.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "cdif.mm"
include "wral.mm"
include "w3a.mm"
include "crab.mm"
include "biid.mm"
include "difeq2.mm"
include "cbvralv.mm"
include "3anbi123i.mm"
include "rabbii.mm"
include "eqtri.mm"
include "isldsys.mm"
include "sylib.mm"
include "simprd.mm"
include "simp3d.mm"
include "prelpwi.mm"
include "rspcdva.mm"
include "mp2and.mm"
include "eqeltrrd.mm"
include "pm2.61dane.mm"

theorem unelldsys
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  let cL: class L
  let cO: class O
  let vs: setvar s
  let vz: setvar z
  let vu: setvar u
  let vt: setvar t
  let cV: class V
  assume isldsys.l: |- L = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s ( O \ x ) e. s /\ A. x e. ~P s ( ( x ~<_ _om /\ Disj_ y e. x y ) -> U. x e. s ) ) }
  assume unelldsys.s: |- ( ph -> S e. L )
  assume unelldsys.a: |- ( ph -> A e. S )
  assume unelldsys.b: |- ( ph -> B e. S )
  assume unelldsys.c: |- ( ph -> ( A i^i B ) = (/) )

  disjoint s x
  disjoint s y
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint s y
  disjoint O s
  disjoint O x
  disjoint s x
  disjoint S s
  disjoint S x
  disjoint s z
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint O z
  disjoint S z
  disjoint ph z
  disjoint s u
  disjoint u y
  disjoint L t
  disjoint O t
  disjoint s t
  disjoint t x
  disjoint V x
  assert |- ( ph -> ( A u. B ) e. S )

  proof
    wph
    cA
    cB
    cun
    #
    cS
    wcel
    cA
    c0
    wph
    cA
    c0
    wceq
    #
    wa
    #
    @0
    cB
    cS
    @2
    @0
    c0
    cB
    cun
    #
    cB
    @1
    @0
    @3
    wceq
    wph
    cA
    c0
    cB
    uneq1
    adantl
    cB
    c0
    cun
    @3
    cB
    cB
    c0
    uncom
    cB
    un0
    eqtr3i
    syl6eq
    wph
    cB
    cS
    wcel
    #
    @1
    unelldsys.b
    adantr
    eqeltrd
    wph
    cA
    c0
    wne
    #
    wa
    #
    cA
    cB
    cpr
    #
    cuni
    #
    @0
    cS
    wph
    @8
    @0
    wceq
    #
    @5
    wph
    cA
    cS
    wcel
    #
    @4
    @9
    unelldsys.a
    unelldsys.b
    cA
    cB
    cS
    cS
    uniprg
    syl2anc
    adantr
    @6
    @7
    com
    cdom
    wbr
    #
    vy
    @7
    vy
    cv
    #
    wdisj
    #
    @8
    cS
    wcel
    #
    wph
    @11
    @5
    wph
    @10
    @4
    @11
    unelldsys.a
    unelldsys.b
    cA
    cB
    cS
    cS
    prct
    syl2anc
    adantr
    @6
    @13
    cA
    cB
    cin
    c0
    wceq
    #
    wph
    @15
    @5
    unelldsys.c
    adantr
    @6
    @10
    @4
    cA
    cB
    wne
    #
    @13
    @15
    wb
    wph
    @10
    @5
    unelldsys.a
    adantr
    wph
    @4
    @5
    unelldsys.b
    adantr
    @6
    vz
    cv
    #
    cA
    wcel
    #
    @16
    vz
    @5
    @18
    vz
    wex
    #
    wph
    @5
    @19
    vz
    cA
    n0
    biimpi
    adantl
    wph
    @18
    @16
    @5
    wph
    @18
    wa
    @17
    cB
    wcel
    wn
    #
    @16
    wph
    @15
    @18
    @20
    unelldsys.c
    cA
    cB
    @17
    disjel
    sylan
    @18
    @20
    @16
    wph
    @17
    cA
    cB
    nelne1
    adantll
    mpdan
    adantlr
    exlimddv
    vy
    cA
    cB
    @12
    cA
    cB
    cS
    @12
    cA
    wceq
    id
    @12
    cB
    wceq
    id
    disjprg
    syl3anc
    mpbird
    wph
    @11
    @13
    wa
    #
    @14
    wi
    #
    @5
    wph
    @17
    com
    cdom
    wbr
    #
    vy
    @17
    @12
    wdisj
    #
    wa
    #
    @17
    cuni
    #
    cS
    wcel
    #
    wi
    #
    @22
    vz
    cS
    cpw
    #
    @7
    @17
    @7
    wceq
    #
    @25
    @21
    @27
    @14
    @30
    @23
    @11
    @24
    @13
    @17
    @7
    com
    cdom
    breq1
    vy
    @17
    @7
    @12
    disjeq1
    anbi12d
    @30
    @26
    @8
    cS
    @17
    @7
    unieq
    eleq1d
    imbi12d
    wph
    c0
    cS
    wcel
    #
    cO
    @17
    cdif
    #
    cS
    wcel
    vz
    cS
    wral
    #
    @28
    vz
    @29
    wral
    #
    wph
    cS
    cO
    cpw
    cpw
    #
    wcel
    #
    @31
    @33
    @34
    w3a
    #
    wph
    cS
    cL
    wcel
    @36
    @37
    wa
    unelldsys.s
    vz
    vy
    cS
    cL
    cO
    vs
    cL
    c0
    vs
    cv
    #
    wcel
    #
    cO
    vx
    cv
    #
    cdif
    #
    @38
    wcel
    #
    vx
    @38
    wral
    #
    @40
    com
    cdom
    wbr
    #
    vy
    @40
    @12
    wdisj
    #
    wa
    #
    @40
    cuni
    #
    @38
    wcel
    #
    wi
    #
    vx
    @38
    cpw
    #
    wral
    #
    w3a
    #
    vs
    @35
    crab
    @39
    @32
    @38
    wcel
    #
    vz
    @38
    wral
    #
    @25
    @26
    @38
    wcel
    #
    wi
    #
    vz
    @50
    wral
    #
    w3a
    #
    vs
    @35
    crab
    isldsys.l
    @52
    @58
    vs
    @35
    @39
    @39
    @43
    @54
    @51
    @57
    @39
    biid
    @42
    @53
    vx
    vz
    @38
    @40
    @17
    wceq
    #
    @41
    @32
    @38
    @40
    @17
    cO
    difeq2
    eleq1d
    cbvralv
    @49
    @56
    vx
    vz
    @50
    @59
    @46
    @25
    @48
    @55
    @59
    @44
    @23
    @45
    @24
    @40
    @17
    com
    cdom
    breq1
    vy
    @40
    @17
    @12
    disjeq1
    anbi12d
    @59
    @47
    @26
    @38
    @40
    @17
    unieq
    eleq1d
    imbi12d
    cbvralv
    3anbi123i
    rabbii
    eqtri
    isldsys
    sylib
    simprd
    simp3d
    wph
    @10
    @4
    @7
    @29
    wcel
    unelldsys.a
    unelldsys.b
    cA
    cB
    cS
    prelpwi
    syl2anc
    rspcdva
    adantr
    mp2and
    eqeltrrd
    pm2.61dane
end
